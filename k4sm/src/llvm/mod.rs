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
    Module, Operand, Terminator, Type, types::{Types, NamedStructDef},
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
            1 => InstructionSize::U8, // boolean
            8 => InstructionSize::U8,
            16 => InstructionSize::U16,
            24 => InstructionSize::U32, // todo?
            32 => InstructionSize::U32,
            64 => InstructionSize::U64,
            128 => InstructionSize::U128,
            48 => InstructionSize::U64, // todo?
            96 => InstructionSize::U128, // todo?
            56 => InstructionSize::U64, // todo?
            x => unreachable!("integer bits {}", x),
        },
        Type::PointerType { .. } => InstructionSize::U64,
        Type::ArrayType { .. } => InstructionSize::U64,
        Type::StructType { .. } => InstructionSize::U64,
        Type::NamedStructType { .. } => InstructionSize::U64,
        Type::FPType(precision) => match precision {
            llvm_ir::types::FPType::Single => InstructionSize::F32,
            llvm_ir::types::FPType::Double => InstructionSize::F64,
            t => todo!("{:?}", t),
        },
        t => todo!("{:?}", t),
    }
}

pub fn size_bytes(typ: &Type, types: &Types, pool: &mut Pool) -> usize {
    // todo: this is the lazy way
    let dummy = Ssa::parse_const(typ, "dummy".to_owned(), types, pool);
    let size = dummy.size_in_bytes();
    pool.take(&dummy.name()).unwrap();
    size
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
        assert!(
            matches!(
                src.as_ref(),
                Ssa::Pointer { .. } | Ssa::StaticPointer { .. }
            ),
            "{:?} is not a pointer",
            src.as_ref()
        );
        let mut ret = if let Some(ret) = self.pool().take(dest_name) {
            // todo!();
            Rc::try_unwrap(ret).unwrap()
        } else {
            // fixme: this is hacky
            self.pool().stack_size += 16;
            let ret = if let Ssa::Pointer {
                // pointee,
                pointee_type,
                ..
            }
            | Ssa::StaticPointer {
                // pointee,
                pointee_type,
                ..
            } = src.as_ref()
            {
                Ssa::Pointer {
                    name: dest_name.to_owned(),
                    stack_offset: self.pool().stack_size,
                    pointee_type: pointee_type.to_owned(),
                }
            } else {
                unreachable!()
            };

            ret
        };

        writeln!(
            self.current_function.body,
            "    mov{} {} {}",
            ret.size(),
            ret,
            src
        )?;

        let ret_fmt = ret.asm_repr();
        let ret_size = ret.size();
        
        let ret_pointee_type = if let Ssa::Pointer {
            pointee_type,
            ..
        } = &mut ret
        {
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
                let tmp = self
                    .pool()
                    .get_unused_register("tmp", InstructionSize::U64)
                    .unwrap();

                let types =&self.module.types.to_owned();
                let pointee_size_bytes = size_bytes(pointee_type, types, self.pool());
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    tmp.size(),
                    tmp,
                    index
                )?;
                writeln!(
                    self.current_function.body,
                    "    mul{} {} ${}",
                    tmp.size(),
                    tmp,
                    pointee_size_bytes,
                )?;
                writeln!(
                    self.current_function.body,
                    "    add{} {} {}",
                    ret_size, ret_fmt, tmp
                )?;
                self.pool().take_back(tmp);
            }
            pointee_type
        } else {
            unreachable!()
        };

        let types = &self.module.types.to_owned();

        macro_rules! struct_type {
            ($idx_idx:expr, $index:expr, $element_types:expr) => {
                // check if we can do the happy path and just grab it at compile time
                match $index.as_ref() {
                    Ssa::Constant { value, .. } => {
                        let index = value.as_qword().get() as usize;
                        if $element_types.is_empty() {
                            // as below, we assume it's an empty u8 array
                            // also as below, this might break things, but what can we really do?
                            assert_eq!($idx_idx, indices.len() - 1);
                            *ret_pointee_type = Type::IntegerType { bits: 8 };
                            break;
                        } else {
                            for elem in &$element_types[..index] {
                                let size = size_bytes(elem, types, self.pool());
                                writeln!(
                                    self.current_function.body,
                                    "    add{} {} ${}",
                                    ret_size,
                                    ret_fmt,
                                    size,
                                )?;
                            }
                            *ret_pointee_type = $element_types[index].as_ref().to_owned();
                            continue;
                        }
                    }
                    Ssa::Register {
                        reg: Register::Rz, ..
                    } => {
                        // VERY happy path, the index is zero, just deref the first element
                        if $element_types.is_empty() {
                            assert_eq!($idx_idx, indices.len() - 1);
                            // points to nothing, we return
                            // todo: we're going to assume it's a bunch of u8's until this breaks
                            *ret_pointee_type = Type::IntegerType { bits: 8 };
                            break;
                        } else {
                            *ret_pointee_type = $element_types[0].as_ref().to_owned();
                        }
                        continue;
                    }
                    _ => {}
                }
                let counter = self
                    .pool()
                    .get_unused_register("counter", InstructionSize::U64)
                    .unwrap();
                writeln!(
                    self.current_function.body,
                    "    mov{} {} rz",
                    counter.size(),
                    counter
                )?;

                // our task here:
                // loop {
                //     compare the counter to the index
                //     if equal, break the loop
                //     else {
                //         add the size of the element to the offset
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
                for elem_type in $element_types.iter() {
                    writeln!(
                        self.current_function.body,
                        "    cmp{} {} {}",
                        counter.size(),
                        counter,
                        $index
                    )?;
                    writeln!(
                        self.current_function.body,
                        "    jeq{} {}",
                        end_label.size(),
                        end_label
                    )?;
                    let size = size_bytes(elem_type, types, self.pool());
                    writeln!(
                        self.current_function.body,
                        "    add{} {} ${}",
                        ret_size,
                        ret_fmt,
                        size,
                    )?;
                    writeln!(
                        self.current_function.body,
                        "    add{} {} $1",
                        counter.size(),
                        counter
                    )?;
                }
                writeln!(self.current_function.body, "{}", end_label)?;

                self.pool().take_back(counter);

                if $element_types.is_empty() {
                    // as below, we assume it's an empty u8 array
                    // also as below, this might break things, but what can we really do?
                    assert_eq!($idx_idx, indices.len() - 1);
                    *ret_pointee_type = Type::IntegerType { bits: 8 };
                    break;
                } else {
                    let type0 = $element_types[0].as_ref().to_owned();
                    if $element_types.iter().all(|elem| *elem.as_ref() == type0) {
                        *ret_pointee_type = type0;
                    } else {
                        todo!()
                    }
                }
            };
        }

        for (idx_idx, index) in indices.iter().enumerate().skip(1) {
            match ret_pointee_type.clone() {
                Type::IntegerType { bits } => {
                    // as with the composite case below, check if the index is const first
                    match index.as_ref() {
                        Ssa::Constant { value, .. } => {
                            let index = value.as_qword().get() as usize;
                            writeln!(
                                self.current_function.body,
                                "    add{} {} ${}",
                                ret_size,
                                ret_fmt,
                                index * InstructionSize::from_n_bits_unsigned(bits).in_bytes()
                            )?;
                            *ret_pointee_type = Type::IntegerType { bits }; // redundant
                            assert_eq!(idx_idx, indices.len() - 1);
                            break;
                        }
                        Ssa::Register {
                            reg: Register::Rz, ..
                        } => {
                            // VERY happy path, the index is zero, just get the first element
                            assert_eq!(idx_idx, indices.len() - 1);
                            *ret_pointee_type = Type::IntegerType { bits }; // redundant
                            break;
                        }
                        _ => todo!(),
                    }
                }
                Type::ArrayType { element_type, num_elements } | Type::VectorType { element_type, num_elements, .. }=> {
                    // as with the composite case below, check if the index is const first
                    match index.as_ref() {
                        Ssa::Constant { value, .. } => {
                            let index = value.as_qword().get() as usize;
                            let size = size_bytes(&element_type, types, self.pool());
                            writeln!(
                                self.current_function.body,
                                "    add{} {} ${}",
                                ret_size, ret_fmt, index * size
                            )?;
                            *ret_pointee_type = element_type.as_ref().to_owned();
                            continue;
                        }
                        Ssa::Register {
                            reg: Register::Rz, ..
                        } => {
                            // VERY happy path, the index is zero, just get the first element
                            *ret_pointee_type = element_type.as_ref().to_owned();
                            continue;
                        }

                        _ => {}
                    }

                    let counter = self
                        .pool()
                        .get_unused_register("counter", InstructionSize::U64)
                        .unwrap();
                    writeln!(
                        self.current_function.body,
                        "    mov{} {} rz",
                        counter.size(),
                        counter
                    )?;

                    // our task here:
                    // loop {
                    //     compare the counter to the index
                    //     if equal, break the loop
                    //     else {
                    //         add the size of the element to the offset
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
                    let size = size_bytes(&element_type, types, self.pool());
                    for _ in 0..num_elements {
                        writeln!(
                            self.current_function.body,
                            "    cmp{} {} {}",
                            counter.size(),
                            counter,
                            index
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    jeq{} {}",
                            end_label.size(),
                            end_label
                        )?;
                        
                        writeln!(
                            self.current_function.body,
                            "    add{} {} ${}",
                            ret_size, ret_fmt,
                            size,
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    add{} {} $1",
                            counter.size(),
                            counter
                        )?;
                    }
                    writeln!(self.current_function.body, "{}", end_label)?;

                    self.pool().take_back(counter);

                    *ret_pointee_type = element_type.as_ref().to_owned();
                }
                Type::NamedStructType { name } => {
                    let typ = self.module.types.named_struct_def(&name).unwrap();
                    if let NamedStructDef::Defined(typ) = typ {
                        if let Type::StructType { element_types, .. } = typ.as_ref().to_owned() {
                            struct_type!(idx_idx, index, element_types);
                        } else {
                            unreachable!()
                        }
                    } else {
                        todo!("{:?}", typ)
                    }
                }
                Type::StructType { element_types, .. } => {
                    struct_type!(idx_idx, index, element_types);
                }
                Type::PointerType { pointee_type, .. } => {
                    if let Ssa::Register {
                        reg: Register::Rz, ..
                    } = index.as_ref()
                    {
                        // fast path
                        // index of 0, we don't add anything
                        *ret_pointee_type = pointee_type.as_ref().to_owned();
                    } else {
                        // we assume it's array-style pointer indexing and offset by the size of its pointee
                        // (what else would it be, really?)
                        let tmp = self
                            .pool()
                            .get_unused_register("tmp", InstructionSize::U64)
                            .unwrap();

                        let size = size_bytes(&pointee_type, types, self.pool());
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} {}",
                            tmp.size(),
                            tmp,
                            index
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mul{} {} ${}",
                            tmp.size(),
                            tmp,
                            size,
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    add{} {} {}",
                            ret_size, ret_fmt, tmp
                        )?;
                        self.pool().take_back(tmp);

                        *ret_pointee_type = pointee_type.as_ref().to_owned();
                    }
                }

                _ => todo!("{:?}", ret_pointee_type),
            }
        }
        let ret = Rc::new(ret);
        self.pool().insert(ret.clone());

        Ok(ret)
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

        for func in self.module.clone().functions.iter() {
            println!();
            self.current_function = Function::default();
            writeln!(self.current_function.prologue, "%{}", func.name)?;
            writeln!(
                self.current_function.prologue,
                "    push{} bp",
                InstructionSize::U64
            )?;
            

            self.current_function.name = func.name.to_owned();
            self.current_function.pool = Pool::new(
                func.parameters.to_owned(),
                &self.module.types.to_owned(),
                &mut self.current_function.body,
            );
            
            for global in globals.iter() {
                self.pool().insert(global.clone());
            }
            self.current_function.last_block = Some(
                self.pool()
                    .get_unused_register("last_block", InstructionSize::U64)
                    .unwrap(),
            );
            writeln!(
                self.current_function.body,
                "    mov{} {} %{}",
                self.current_function.last_block.as_ref().unwrap().size(),
                self.current_function.last_block.as_ref().unwrap(),
                self.current_function.name
            )?;
            println!("Function {}", self.current_function.name);
            for block in func.basic_blocks.iter() {
                let name = &block.name.to_string()[1..];
                let func_name = self.current_function.name.clone();
                let block_ssa = self.pool().label(&func_name, name);
                writeln!(self.current_function.body, "{}", block_ssa)?;

                for instr in block.instrs.iter() {
                    println!("  {}", instr);
                    self.parse_instr(instr)?;
                }
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    self.current_function.last_block.as_ref().unwrap().size(),
                    self.current_function.last_block.as_ref().unwrap(),
                    block_ssa
                )?;
                writeln!(self.current_function.body, "; {}", block.term)?;
                match &block.term {
                    Terminator::Ret(Ret { return_operand, .. }) => {
                        writeln!(
                            self.current_function.epilogue,
                            "%{}_ret",
                            self.current_function.name
                        )?;
                        if let Some(ret) = return_operand.as_ref() {
                            let ret = self.parse_operand(None, ret, true)?;
                            writeln!(
                                self.current_function.epilogue,
                                "    mov{} ra {}",
                                ret.size(),
                                ret
                            )?;
                        }
                        writeln!(
                            self.current_function.body,
                            "    jmp{} %{}_ret",
                            InstructionSize::U64,
                            self.current_function.name
                        )?;
                    }
                    Terminator::CondBr(CondBr {
                        condition,
                        true_dest,
                        false_dest,
                        ..
                    }) => {
                        let cond = self.parse_operand(None, condition, false)?;
                        let func_name = self.current_function.name.clone();
                        let true_dest = self
                            .pool()
                            .label(&func_name, &true_dest.to_owned().to_string());
                        let false_dest = self
                            .pool()
                            .label(&func_name, &false_dest.to_owned().to_string());
                        writeln!(
                            self.current_function.body,
                            "    cmp{} {} rz",
                            cond.size(),
                            cond
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    jeq{} {}",
                            false_dest.size(),
                            false_dest
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    jmp{} {}",
                            true_dest.size(),
                            true_dest
                        )?;
                    }
                    Terminator::Br(Br { dest, .. }) => {
                        let func_name = self.current_function.name.clone();
                        let dest = self.pool().label(&func_name, &dest.to_owned().to_string());
                        writeln!(
                            self.current_function.body,
                            "    jmp{} {}",
                            dest.size(),
                            dest
                        )?;
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
                            let func_name = self.current_function.name.clone();
                            let dest = self.pool().label(&func_name, &dest.to_owned().to_string());
                            writeln!(
                                self.current_function.body,
                                "    cmp{} {} {}",
                                op.size(),
                                op,
                                opt
                            )?;
                            writeln!(
                                self.current_function.body,
                                "    jeq{} {}",
                                dest.size(),
                                dest
                            )?;
                        }
                        let func_name = self.current_function.name.clone();
                        let default = self.pool().label(&func_name, &switch.default_dest.to_owned().to_string());
                        writeln!(
                            self.current_function.body,
                            "    jmp{} {}",
                            default.size(),
                            default
                        )?;
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
                writeln!(
                    self.current_function.prologue,
                    "    push{} {}",
                    InstructionSize::U64,
                    reg
                )?;
            }
            writeln!(
                self.current_function.prologue,
                "    mov{} bp sp",
                InstructionSize::U64
            )?;
            
            if sp != 0 {
                writeln!(
                    self.current_function.prologue,
                    "    sub{} sp ${}",
                    InstructionSize::U64,
                    sp
                )?;
            }
            writeln!(
                self.current_function.epilogue,
                "    mov{} sp bp",
                InstructionSize::U64
            )?;
            for reg in clobbered_regs.iter().rev() {
                writeln!(
                    self.current_function.epilogue,
                    "    pop{} {}",
                    InstructionSize::U64,
                    reg
                )?;
            }

            writeln!(
                self.current_function.epilogue,
                "    pop{} bp",
                InstructionSize::U64
            )?;
            writeln!(self.current_function.epilogue, "    ret")?;

            write!(self.output, "{}", self.current_function.prologue)?;
            write!(self.output, "{}", self.current_function.body)?;
            writeln!(self.output, "{}", self.current_function.epilogue)?;
        }

        Ok(self.output.clone())
    }
}
