use std::{
    error::Error,
    fmt::Write,
    path::Path,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

use k4s::InstructionSize;
use llvm_ir::{
    terminator::{Br, CondBr, Ret},
    Module, Operand, Terminator, Type,
};

use crate::llvm::ssa::Register;

use self::{pool::Pool, ssa::Ssa};

pub mod parse_instr;
pub mod parse_operand;
pub mod pool;
pub mod ssa;

#[inline]
pub fn op_size(typ: &Type) -> InstructionSize {
    match typ {
        Type::IntegerType { bits } => match *bits {
            1 => InstructionSize::Byte, // boolean
            8 => InstructionSize::Byte,
            16 => InstructionSize::Word,
            32 => InstructionSize::Dword,
            64 => InstructionSize::Qword,
            x => unreachable!("integer bits {}", x),
        },
        Type::PointerType { .. } => InstructionSize::Qword,
        Type::ArrayType { .. } => InstructionSize::Qword,
        Type::StructType { .. } => InstructionSize::Qword,
        Type::NamedStructType { .. } => InstructionSize::Qword,
        Type::FPType(precision) => match precision {
            llvm_ir::types::FPType::Single => InstructionSize::Dword,
            llvm_ir::types::FPType::Double => InstructionSize::Qword,
            t => todo!("{:?}", t),
        },
        t => todo!("{:?}", t),
    }
}

#[derive(Default)]
pub struct Function {
    name: String,

    prologue: String,
    body: String,
    epilogue: String,

    pool: Pool,
    last_block: Option<Rc<Ssa>>,
}

pub struct Parser {
    module: Module,
    output: String,

    id_counter: AtomicUsize,
    current_function: Function,
}

impl Parser {
    pub fn new(bc_path: impl AsRef<Path>) -> Self {
        Self {
            module: Module::from_bc_path(bc_path).unwrap(),
            output: String::new(),
            id_counter: AtomicUsize::new(0),
            current_function: Function::default(),
        }
    }

    fn alloc_id(&self) -> usize {
        self.id_counter.fetch_add(1, Ordering::SeqCst)
    }

    fn pool(&mut self) -> &mut Pool {
        &mut self.current_function.pool
    }

    fn get_element_ptr(
        &mut self,
        dest_name: &str,
        src: Rc<Ssa>,
        indices: Vec<Rc<Ssa>>,
    ) -> Result<Rc<Ssa>, Box<dyn Error>> {
        assert!(matches!(src.as_ref(), Ssa::Pointer { .. } | Ssa::StaticPointer { .. }), "{:?} is not a pointer", src.as_ref());
        let mut ret = if let Some(ref mut addr_next) = self.pool().take(dest_name) {
            Rc::get_mut(addr_next).unwrap().clone()
        } else {
            self.pool().stack_size += 16;
            let addr_next = 
            if let Ssa::Pointer { pointee, .. } | Ssa::StaticPointer {  pointee, .. } = src.as_ref() {
                Ssa::Pointer { name: dest_name.to_owned(), stack_offset: self.pool().stack_size, pointee: pointee.clone() }  
            } else {
                unreachable!()
            };
            
            addr_next
        };
        
        if let Some(off) = src.stack_offset() {
            writeln!(self.current_function.body, "    mov q {} bp", ret)?;
            writeln!(self.current_function.body, "    sub q {} ${}", ret, off)?;
        } else {
            match src.as_ref() {
                Ssa::Label { .. } => {
                    writeln!(self.current_function.body, "    mov q {} {}", ret, src)?;
                }
                Ssa::StaticComposite { .. } => {
                    writeln!(self.current_function.body, "    mov q {} {}", ret, src)?;
                }
                Ssa::StaticFunction { .. } => {
                    writeln!(self.current_function.body, "    mov q {} {}", ret, src)?;
                }
                Ssa::StaticPointer { .. } => {
                    writeln!(self.current_function.body, "    mov q {} {}", ret, src)?;
                }
                _ => todo!("{:?}", src.as_ref())
            }
        }

        let ret_fmt = ret.asm_repr();
        let ret_pointee = if let Ssa::Pointer { pointee, .. } = &mut ret {
            let ret_pointee = pointee.as_mut().unwrap();
            let index = &indices[0];
            if let Ssa::Register {
                reg: Register::Rz, ..
            } = index.as_ref()
            {
                // fast path
                // index of 0, we don't add anything
            } else {
                // we assume it's array-style pointer indexing and offset by the size of its pointee
                // (what else would it be, really?)
                let tmp = self.pool().get_unused_register("tmp", InstructionSize::Qword).unwrap();

                writeln!(self.current_function.body, "    mov q {} {}", tmp, index)?;
                writeln!(self.current_function.body, "    mul q {} ${}", tmp, ret_pointee.size_in_bytes())?;
                writeln!(self.current_function.body, "    add q {} {}", ret_fmt, tmp)?;
                if ret_pointee.stack_offset().is_some() {
                    // todo: make this obey the rule that `getelementptr` doesn't access memory
                    writeln!(self.current_function.body, "    mov q {} {}", tmp, ret_fmt)?;
                    writeln!(self.current_function.body, "    mov{} {} [{}]", ret_pointee.size(), ret_pointee, tmp)?;
                }
                self.pool().take_back(&tmp.name(), tmp);
            }
            ret_pointee
        } else {
            unreachable!()
        };

        
        
        for (idx_idx, index) in indices.iter().enumerate().skip(1) {
            match ret_pointee.as_ref().clone() {
                Ssa::Primitive { size, .. } => {
                    // as with the composite case below, check if the index is const first
                    match index.as_ref() {
                        Ssa::Constant { value, .. } => {
                            let index = value.as_qword().get() as usize;
                            writeln!(self.current_function.body, "    add q {} ${}", ret_fmt, index * size.in_bytes())?;
                            assert_eq!(idx_idx, indices.len()-1);
                            let mut new_pointee = ret_pointee.duplicate(&format!("{}_pointee_{}", src.name(), self.alloc_id()));
                            if let Some(stack_offset) = new_pointee.stack_offset_mut() {
                                *stack_offset += index * size.in_bytes();
                            } else {
                                unreachable!()
                            }
                            let new_pointee = Rc::new(new_pointee);
                            self.pool().insert(new_pointee.clone());
                            *ret_pointee = new_pointee;
                            break;
                        }
                        Ssa::Register { reg: Register::Rz, .. } => {
                            // VERY happy path, the index is zero, just get the first element
                            assert_eq!(idx_idx, indices.len()-1);
                            break;
                        }
                        _ => todo!()
                    }
                }
                Ssa::Data { .. } => {
                    // as with the composite case below, check if the index is const first
                    match index.as_ref() {
                        Ssa::Constant { value, .. } => {
                            let index = value.as_qword().get() as usize;
                            writeln!(self.current_function.body, "    add q {} ${}", ret_fmt, index)?;
                            assert_eq!(idx_idx, indices.len()-1);

                            break;
                        }
                        Ssa::Register { reg: Register::Rz, .. } => {
                            // VERY happy path, the index is zero, just get the first element
                            assert_eq!(idx_idx, indices.len()-1);
                            break;
                        }
                        _ => todo!()
                    }
                }
                Ssa::Composite { ref elements, .. } | Ssa::StaticComposite { ref elements, .. }=> {
                    // check if we can do the happy path and just grab it at compile time
                    match index.as_ref() {
                        Ssa::Constant { value, .. } => {
                            let index = value.as_qword().get() as usize;
                            for elem in &elements[..index] {
                                writeln!(self.current_function.body, "    add q {} ${}", ret_fmt, elem.size_in_bytes())?;
                            }
                            *ret_pointee = elements[index].clone();
                            continue;
                        }
                        Ssa::Register { reg: Register::Rz, .. } => {
                            // VERY happy path, the index is zero, just deref the first element
                            *ret_pointee = elements[0].clone();
                            continue;
                        }
                        _ => {}
                    }
                    let counter = self
                        .pool()
                        .get_unused_register("counter", InstructionSize::Qword)
                        .unwrap();
                    writeln!(self.current_function.body, "    mov q {} rz", counter)?;

                    // our task here:
                    // loop {
                    //     compare the counter to the index
                    //     if equal, break the loop
                    //     else {
                    //         subtract the size of the element to the offset (goes backwards)
                    //         increment counter by 1
                    //     }
                    // }
                    // *** this will need to be an unrolled loop in the assembly code, unfortunately, but we can use a for loop here
                    let id = self.alloc_id();
                    let func_name = self.current_function.name.to_owned();
                    let end_label = self.pool().label(
                        &func_name,
                        &format!("_struct_index_{}_end_{}", src.name(), id),
                    );
                    for elem in elements {
                        writeln!(
                            self.current_function.body,
                            "    cmp q {} {}",
                            counter, index
                        )?;
                        writeln!(self.current_function.body, "    jeq q {}", end_label)?;
                        writeln!(
                            self.current_function.body,
                            "    add q {} ${}",
                            ret_fmt,
                            elem.size_in_bytes()
                        )?;
                        writeln!(self.current_function.body, "    add q {} $1", counter)?;
                    }
                    writeln!(self.current_function.body, "{}", end_label)?;
                    
                    self.pool().take_back(&counter.name(), counter);

                    todo!("update addr_next to be the pointed element when index is not const");
                }
                Ssa::Pointer {
                    pointee,
                    ..
                } | Ssa::StaticPointer { pointee, .. } => {
                    let pointee = pointee.as_ref().unwrap();
                    if let Ssa::Register {
                        reg: Register::Rz, ..
                    } = index.as_ref()
                    {
                        // fast path
                        // index of 0, we don't add anything
                        *ret_pointee = pointee.clone();
                    } else {
                        // we assume it's array-style pointer indexing and offset by the size of its pointee
                        // (what else would it be, really?)
                        let tmp = self.pool().get_unused_register("tmp", InstructionSize::Qword).unwrap();

                        writeln!(self.current_function.body, "    mov q {} {}", tmp, index)?;
                        writeln!(self.current_function.body, "    mul q {} ${}", tmp, pointee.size_in_bytes())?;
                        writeln!(self.current_function.body, "    add q {} {}", ret_fmt, tmp)?;
                        self.pool().take_back(&tmp.name(), tmp);

                        // we need to get the stack offset of the base pointee, subtract the index * size from it, and make our new src [-new_stack_offset+bp]
                        // we already did the first two parts! see the chunk of code with `tmp` above
                        // the value we need == `offset` already
                        let new_src = pointee.duplicate(&format!("{}_new_src_{}", src, self.alloc_id()));
                        // if new_src.stack_offset_mut().is_some() {
                        //     // todo: make this obey the rule that `getelementptr` doesn't access memory
                            let new_src = Rc::new(new_src);
                        //     let tmp2 = self.pool().get_unused_register("tmp2", InstructionSize::Qword).unwrap();
                        //     writeln!(self.current_function.body, "    mov q {} {}", tmp2, ret_fmt)?;
                        //     writeln!(self.current_function.body, "    mov q {} [{}]", new_src, tmp2)?;
                        //     self.pool().take_back(&tmp2.name(), tmp2);
                        //     *ret_pointee = new_src;
                        // } else {
                        //     todo!()
                        // }
                        *ret_pointee = new_src;
                    }
                }
                
                _ => todo!("{:?}", ret_pointee)
            }
        }
        let addr_next = Rc::new(ret);
        self.pool().insert(addr_next.clone());
        
        Ok(addr_next)
    }

    fn get_or_else(&mut self, name: &str, mut f: impl FnMut(&mut Pool) -> Rc<Ssa>) -> Rc<Ssa> {
        if let Some(ssa) = self.current_function.pool.get(name) {
            ssa.clone()
        } else {
            f(self.pool())
        }
    }

    pub fn emit_k4sm(&mut self) -> Result<String, Box<dyn Error>> {
        let mut globals = Vec::new();
        for global in self.module.clone().global_vars.iter() {
            let data = self.parse_operand(
                Some(global.name.to_owned()),
                &Operand::ConstantOperand(global.initializer.as_ref().unwrap().to_owned()),
                false,
            )?;
            globals.push(data);
        }

        writeln!(self.output)?;

        self.current_function = Function::default();

        for func in self.module.clone().functions.iter() {
            println!();
            self.current_function = Function::default();
            writeln!(self.current_function.prologue, "%{}", func.name)?;
            writeln!(self.current_function.prologue, "    push q bp")?;
            // writeln!(self.current_function.prologue, "    mov q bp sp")?;

            self.current_function.name = func.name.to_owned();
            self.current_function.pool =
                Pool::new(func.parameters.to_owned(), &self.module.types.to_owned(), &mut self.current_function.body);
            for global in globals.iter() {
                self.pool().insert(global.clone());
            }
            self.current_function.last_block = Some(
                self.pool()
                    .get_unused_register("last_block", InstructionSize::Qword)
                    .unwrap(),
            );
            writeln!(
                self.current_function.body,
                "    mov q {} %{}",
                self.current_function.last_block.as_ref().unwrap(),
                func.name
            )?;
            println!("Function {}", self.current_function.name);
            for block in func.basic_blocks.iter() {
                let block_ssa = self.pool().label(&func.name, &block.name.to_string()[1..]);
                writeln!(self.current_function.body, "{}", block_ssa)?;

                for instr in block.instrs.iter() {
                    println!("  {}", instr);
                    self.parse_instr(instr)?;
                }
                writeln!(
                    self.current_function.body,
                    "    mov q {} {}",
                    self.current_function.last_block.as_ref().unwrap(),
                    block_ssa
                )?;
                match &block.term {
                    Terminator::Ret(Ret { return_operand, .. }) => {
                        writeln!(self.current_function.epilogue, "%{}_ret", self.current_function.name)?;
                        if let Some(ret) = return_operand.as_ref() {
                            let ret = self.parse_operand(None, ret, true)?;
                            writeln!(
                                self.current_function.epilogue,
                                "    mov{} ra {}",
                                ret.size(),
                                ret
                            )?;
                        }
                        writeln!(self.current_function.body, "    jmp q %{}_ret", self.current_function.name)?;
                        
                    }
                    Terminator::CondBr(CondBr {
                        condition,
                        true_dest,
                        false_dest,
                        ..
                    }) => {
                        let cond = self.parse_operand(None, condition, true)?;
                        let true_dest = self
                            .pool()
                            .label(&func.name, &true_dest.to_owned().to_string());
                        let false_dest = self
                            .pool()
                            .label(&func.name, &false_dest.to_owned().to_string());
                        writeln!(
                            self.current_function.body,
                            "    cmp{} {} rz",
                            cond.size(),
                            cond
                        )?;
                        writeln!(self.current_function.body, "    jeq q {}", false_dest)?;
                        writeln!(self.current_function.body, "    jmp q {}", true_dest)?;
                    }
                    Terminator::Br(Br { dest, .. }) => {
                        let dest = self.pool().label(&func.name, &dest.to_string());
                        writeln!(self.current_function.body, "    jmp q {}", dest)?;
                    }
                    Terminator::Unreachable(_) => {
                        writeln!(self.current_function.body, "    und")?;
                    }
                    Terminator::Switch(switch) => {
                        let op = self.parse_operand(None, &switch.operand, true)?;
                        for (opt, dest) in switch.dests.iter() {
                            let opt = self.parse_operand(
                                None,
                                &Operand::ConstantOperand(opt.to_owned()),
                                false,
                            )?;
                            let dest = self.pool().label(&func.name, &dest.to_string());
                            writeln!(
                                self.current_function.body,
                                "    cmp{} {} {}",
                                op.size(),
                                op,
                                opt
                            )?;
                            writeln!(self.current_function.body, "    jeq q {}", dest)?;
                        }
                        let default = self
                            .pool()
                            .label(&func.name, &switch.default_dest.to_string());
                        writeln!(self.current_function.body, "    jmp q {}", default)?;
                    }
                    x => todo!("{}", x),
                };
            }

            let sp = self.pool().stack_size;
            let clobbered_regs = self
                .pool()
                .clobbered_regs()
                .iter()
                .cloned()
                .collect::<Vec<Register>>();
            for reg in clobbered_regs.iter() {
                writeln!(self.current_function.prologue, "    push q {}", reg)?;
            }
            
            if sp != 0 {

                writeln!(self.current_function.prologue, "    mov q bp sp")?;
                writeln!(self.current_function.prologue, "    sub q sp ${}", sp)?;
                
                writeln!(self.current_function.epilogue, "    mov q sp bp")?;
            }
            for reg in clobbered_regs.iter().rev() {
                writeln!(self.current_function.epilogue, "    pop q {}", reg)?;
            }

            writeln!(self.current_function.epilogue, "    pop q bp")?;
            writeln!(self.current_function.epilogue, "    ret")?;

            write!(self.output, "{}", self.current_function.prologue)?;
            write!(self.output, "{}", self.current_function.body)?;
            writeln!(self.output, "{}", self.current_function.epilogue)?;
        }

        Ok(self.output.clone())
    }
}
