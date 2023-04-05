use std::{
    collections::HashMap,
    error::Error,
    fmt::Write,
    path::Path,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

use k4s::{InstructionSize, Literal};
use llvm_ir::{
    terminator::{Br, CondBr, Ret}, Module, Operand, Terminator, Type,
};

use crate::llvm::ssa::Register;

use self::{pool::Pool, ssa::Ssa};

pub mod pool;
pub mod ssa;
pub mod parse_instr;
pub mod parse_operand;

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
        Type::ArrayType { .. } => todo!(),
        Type::StructType { .. } => InstructionSize::Unsized,
        Type::NamedStructType { .. } => InstructionSize::Unsized,
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

    label_count: usize,
}

pub struct Parser {
    module: Module,
    output: String,

    anon_datas: AtomicUsize,
    current_function: Function,
}

impl Parser {
    pub fn new(bc_path: impl AsRef<Path>) -> Self {
        Self {
            module: Module::from_bc_path(bc_path).unwrap(),
            output: String::new(),
            anon_datas: AtomicUsize::new(0),
            current_function: Function::default(),
        }
    }

    fn pool(&mut self) -> &mut Pool {
        &mut self.current_function.pool
    }


    fn get_element_ptr_const(
        &mut self,
        mut src: Rc<Ssa>,
        indices: Vec<Rc<Ssa>>,
    ) -> Result<Rc<Ssa>, Box<dyn Error>> {
        let mut offset = 0;
        for index in indices.iter() {
            let index = if let Ssa::Constant { value, .. } = index.as_ref() {
                value.as_qword().get() as usize
            } else if let Ssa::Register {
                reg: Register::Rz, ..
            } = index.as_ref()
            {
                0
            } else {
                todo!("{:?}", index)
            };

            match src.as_ref() {
                Ssa::Composite {
                    stack_offset,
                    ref elements,
                    ..
                } => {
                    offset = *stack_offset;
                    for elem in &elements[..index] {
                        offset -= elem.size_in_bytes();
                    }

                    // todo: how do we assign `src` to the element at `index`?
                }
                Ssa::Pointer {
                    stack_offset: _,
                    pointee,
                    ..
                } => {
                    assert_eq!(index, 0, "Attempt to index further than 0 into a pointer");

                    src = pointee.clone();
                }
                _ => {}
            }
        }

        let offset = Rc::new(Ssa::Constant {
            name: format!("{}_offset", src.name()),
            value: Literal::Qword((offset as u64).into()),
            signed: false,
        });
        Ok(offset)
    }

    fn get_element_ptr(
        &mut self,
        mut src: Rc<Ssa>,
        indices: Vec<Rc<Ssa>>,
    ) -> Result<Rc<Ssa>, Box<dyn Error>> {
        let id = self.anon_datas.fetch_add(1, Ordering::SeqCst);
        let offset = self.pool().push_primitive(
            &format!("{}_offset_{}", src.name(), id),
            Literal::default_for_size(InstructionSize::Qword),
            false,
        );
        if let Some(off) = src.stack_offset() {
            writeln!(self.current_function.body, "    mov q {} ${}", offset, off)?;
        }
        for index in indices.iter() {
            match src.as_ref() {
                Ssa::Composite { ref elements, .. } => {
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
                    let id = self.anon_datas.fetch_add(1, Ordering::SeqCst);
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
                            "    sub q {} ${}",
                            offset,
                            elem.size_in_bytes()
                        )?;
                        writeln!(self.current_function.body, "    add q {} $1", counter)?;
                    }
                    writeln!(self.current_function.body, "{}", end_label)?;

                    self.pool().take_back(&counter.name(), counter);
                }
                Ssa::Pointer {
                    stack_offset: _,
                    pointee,
                    ..
                } => {
                    if let Ssa::Register {
                        reg: Register::Rz, ..
                    } = index.as_ref()
                    {
                        // fast path
                        // index of 0, we don't add anything
                    } else {
                        todo!()
                    }

                    src = pointee.clone();
                }
                _ => {}
            }
        }
        Ok(offset)
    }


    fn get_or_push_primitive(&mut self, name: &str, value: Literal) -> Rc<Ssa> {
        if let Some(ssa) = self.pool().get(name) {
            ssa
        } else {
            self.pool().push_primitive(name, value, false)
        }
    }

    pub fn emit_k4sm(&mut self) -> Result<String, Box<dyn Error>> {
        let mut globals = HashMap::new();
        for global in self.module.clone().global_vars.iter() {
            let data = self.parse_operand(
                Some(global.name.to_owned()),
                &Operand::ConstantOperand(global.initializer.as_ref().unwrap().to_owned()),
                false,
            )?;
            globals.insert(data.display(), data);
        }

        writeln!(self.output)?;

        self.current_function = Function::default();

        for func in self.module.clone().functions.iter() {
            println!();
            self.current_function = Function::default();
            writeln!(self.current_function.prologue, "%{}", func.name)?;
            writeln!(self.current_function.prologue, "    push q bp")?;
            writeln!(self.current_function.prologue, "    mov q bp sp")?;

            self.current_function.name = func.name.to_owned();
            self.current_function.pool =
                Pool::new(func.parameters.to_owned(), &mut self.current_function.body);
            for (_name, global) in globals.iter() {
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
                self.current_function.last_block.as_ref().unwrap().display(),
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
                    self.current_function.last_block.as_ref().unwrap().display(),
                    block_ssa
                )?;
                match &block.term {
                    Terminator::Ret(Ret { return_operand, .. }) => {
                        if let Some(ret) = return_operand.as_ref() {
                            let ret = self.parse_operand(None, ret, true)?;
                            writeln!(
                                self.current_function.epilogue,
                                "    mov{} ra {}",
                                ret.size(),
                                ret
                            )?;
                        }
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
            if sp != 0 {
                writeln!(self.current_function.prologue, "    sub q sp ${}", sp)?;
                writeln!(self.current_function.epilogue, "    add q sp ${}", sp)?;
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
