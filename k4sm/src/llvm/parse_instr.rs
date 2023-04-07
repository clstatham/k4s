use std::{error::Error, fmt::Write, rc::Rc};

use k4s::InstructionSize;
use llvm_ir::{types::Typed, FPPredicate, Instruction, IntPredicate, Operand, Type};

use crate::llvm::{
    op_size,
    ssa::{Register, Ssa},
};

use super::Parser;

impl Parser {
    pub fn parse_instr(&mut self, instr: &Instruction) -> Result<(), Box<dyn Error>> {
        macro_rules! match_arith {
            ($instr:expr, $mn:literal) => {{
                let a = self.parse_operand(None, &$instr.operand0, false)?;
                let b = self.parse_operand(None, &$instr.operand1, false)?;
                assert_eq!(a.size(), b.size());
                let dst = self.get_or_else(&$instr.dest.to_string(), |pool| {
                    pool.push_primitive(&$instr.dest.to_string(), a.size(), false)
                });

                writeln!(
                    &mut self.current_function.body,
                    "    mov{} {} {}",
                    dst.size(),
                    dst,
                    a
                )?;
                writeln!(
                    &mut self.current_function.body,
                    concat!("    ", $mn, "{} {} {}"),
                    dst.size(),
                    dst,
                    b
                )?;
            }};
        }
        let function_name = self.current_function.name.to_owned();
        let last_block = self.current_function.last_block.as_ref().unwrap().clone();
        writeln!(self.current_function.body, "; {}", instr)?;
        match instr {
            Instruction::Alloca(instr) => {
                // this is a pointer
                let count = self.parse_operand(None, &instr.num_elements, false)?;
                let count = if let Ssa::Constant { value, .. } = count.as_ref() {
                    value.as_qword().get() as usize
                } else {
                    todo!("{:?}", count)
                };
                assert_eq!(count, 1);

                let ssa = Ssa::push(
                    &instr.allocated_type,
                    format!("{}_pointee", &instr.dest.to_string()),
                    &self.module.types.to_owned(),
                    self.pool(),
                );
                let off = ssa.stack_offset().unwrap();
                let ptr = self.pool().push_pointer(
                    &instr.dest.to_string(),
                    instr.allocated_type.as_ref().to_owned(),
                );
                let tmp = self
                    .pool()
                    .get_unused_register("tmp", InstructionSize::U64)
                    .unwrap();
                writeln!(
                    self.current_function.body,
                    "    mov{} {} bp",
                    tmp.size(),
                    tmp
                )?;
                writeln!(
                    self.current_function.body,
                    "    sub{} {} ${}",
                    tmp.size(),
                    tmp,
                    off
                )?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    ptr.size(),
                    ptr,
                    tmp
                )?;
                self.pool().take_back(tmp);
            }
            Instruction::Store(instr) => {
                let dst = self.parse_operand(None, &instr.address, true)?;
                let src = self.parse_operand(None, &instr.value, false)?;
                match (src.stack_offset(), dst.stack_offset()) {
                    (Some(_), Some(_)) => {
                        let tmp1 = self
                            .pool()
                            .get_unused_register("tmp1", InstructionSize::U64)
                            .unwrap();
                        writeln!(self.current_function.body, "; [{}] <= {}", dst, src)?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} {}",
                            tmp1.size(),
                            tmp1,
                            dst
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            tmp1.size(),
                            tmp1,
                            src
                        )?;
                        self.pool().take_back(tmp1);
                    }
                    (Some(_), None) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            dst.size(),
                            dst,
                            src
                        )?;
                    }
                    (None, Some(_)) => {
                        let tmp1 = self
                            .pool()
                            .get_unused_register("tmp1", InstructionSize::U64)
                            .unwrap();
                        writeln!(self.current_function.body, "; [{}] <= {}", dst, src)?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} {}",
                            tmp1.size(),
                            tmp1,
                            dst,
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            tmp1.size(),
                            tmp1,
                            src
                        )?;
                        self.pool().take_back(tmp1);
                    }
                    (None, None) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            dst.size(),
                            dst,
                            src
                        )?;
                    }
                }
            }
            Instruction::Load(instr) => {
                let src = self.parse_operand(None, &instr.address, true)?;
                let dst = if let Ssa::Pointer { pointee_type, .. }
                | Ssa::StaticPointer { pointee_type, .. } = src.as_ref()
                {
                    // pointee.as_ref().unwrap().duplicate(&instr.dest.to_string())
                    let types = &self.module.types.to_owned();
                    // dbg!(pointee_type);
                    Ssa::push(pointee_type, instr.dest.to_string(), types, self.pool())
                } else {
                    todo!("{:?}", src.as_ref())
                };
                // dbg!(instr.dest.to_string());
                // dbg!(dst.as_ref());
                // let dst = self.pool().push(dst);

                match (src.stack_offset(), dst.stack_offset()) {
                    (Some(src_off), Some(dst_off)) => {
                        let tmp = self
                            .pool()
                            .get_unused_register("tmp", InstructionSize::U64)
                            .unwrap();
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [-{}+bp]",
                            tmp.size(),
                            tmp,
                            src_off
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} [-{}+bp] [{}]",
                            dst.size(),
                            dst_off,
                            tmp
                        )?;
                        self.pool().take_back(tmp);
                    }
                    (Some(src_off), None) => {
                        let tmp = self
                            .pool()
                            .get_unused_register("tmp", InstructionSize::U64)
                            .unwrap();
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [-{}+bp]",
                            tmp.size(),
                            tmp,
                            src_off
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [{}]",
                            dst.size(),
                            dst,
                            tmp
                        )?;
                        self.pool().take_back(tmp);
                    }
                    (None, Some(dst_off)) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} [-{}+bp] [{}]",
                            dst.size(),
                            dst_off,
                            src
                        )?;
                    }
                    (None, None) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [{}]",
                            dst.size(),
                            dst,
                            src
                        )?;
                    }
                }
            }
            Instruction::Add(instr) => match_arith!(instr, "add"),
            Instruction::Sub(instr) => match_arith!(instr, "sub"),
            Instruction::Mul(instr) => match_arith!(instr, "mul"),
            Instruction::UDiv(instr) => match_arith!(instr, "div"),
            Instruction::SDiv(instr) => match_arith!(instr, "sdiv"),
            Instruction::URem(instr) => match_arith!(instr, "mod"),
            Instruction::SRem(instr) => match_arith!(instr, "smod"),
            Instruction::Shl(instr) => match_arith!(instr, "shl"),
            Instruction::LShr(instr) => match_arith!(instr, "shr"),
            Instruction::AShr(instr) => match_arith!(instr, "sshr"),
            Instruction::Or(instr) => match_arith!(instr, "or"),
            Instruction::And(instr) => match_arith!(instr, "and"),
            Instruction::Xor(instr) => match_arith!(instr, "xor"),

            Instruction::FAdd(instr) => match_arith!(instr, "add"),
            Instruction::FSub(instr) => match_arith!(instr, "sub"),
            Instruction::FMul(instr) => match_arith!(instr, "mul"),
            Instruction::FDiv(instr) => match_arith!(instr, "div"),

            Instruction::ICmp(instr) => {
                let a = self.parse_operand(None, &instr.operand0, false)?;
                let b = self.parse_operand(None, &instr.operand1, false)?;
                let size = std::cmp::max(a.size(), b.size());
                let predicate = match instr.predicate {
                    IntPredicate::EQ => "jeq",
                    IntPredicate::ULT | IntPredicate::SLT => "jlt",
                    IntPredicate::UGT | IntPredicate::SGT => "jgt",
                    IntPredicate::UGE | IntPredicate::SGE => "jge",
                    IntPredicate::ULE | IntPredicate::SLE => "jle",
                    IntPredicate::NE => "jne",
                };
                let comparison = match instr.predicate {
                    IntPredicate::SGE | IntPredicate::SLE => "scmp",
                    _ => "cmp",
                };
                let label_id = self.alloc_id();
                let dest = self.get_or_else(&instr.dest.to_string(), |pool| {
                    pool.push_primitive(&instr.dest.to_string(), InstructionSize::U8, false)
                });
                let id = self.alloc_id();
                let true_dest_name = format!("__{label_id}_cmp_true{}", id);
                let false_dest_name = format!("__{label_id}_cmp_false{}", id);
                let end_dest_name = format!("__{label_id}_cmp_end{}", id);
                let true_dest = self.pool().label(&function_name, &true_dest_name);
                let false_dest = self.pool().label(&function_name, &false_dest_name);
                let end_dest = self.pool().label(&function_name, &end_dest_name);

                writeln!(
                    self.current_function.body,
                    "    {}{} {} {}",
                    comparison, size, a, b
                )?;
                writeln!(
                    self.current_function.body,
                    "    {}{} {}",
                    predicate,
                    true_dest.size(),
                    true_dest
                )?;
                writeln!(
                    self.current_function.body,
                    "    jmp{} {}",
                    false_dest.size(),
                    false_dest
                )?;
                writeln!(self.current_function.body, "{}", true_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} $1",
                    dest.size(),
                    dest
                )?;
                writeln!(
                    self.current_function.body,
                    "    jmp{} {}",
                    end_dest.size(),
                    end_dest
                )?;
                writeln!(self.current_function.body, "{}", false_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} rz",
                    dest.size(),
                    dest
                )?;
                writeln!(self.current_function.body, "{}", end_dest)?;
            }
            Instruction::FCmp(instr) => {
                let a = self.parse_operand(None, &instr.operand0, false)?;
                let b = self.parse_operand(None, &instr.operand1, false)?;
                let size = std::cmp::max(a.size(), b.size());
                let predicate = match instr.predicate {
                    FPPredicate::UNO => "juno",
                    FPPredicate::ORD => "jord",
                    FPPredicate::OEQ => "jordeq",
                    FPPredicate::ONE => "jordneq",
                    FPPredicate::OGE => "jordge",
                    FPPredicate::OGT => "jordgt",
                    FPPredicate::OLE => "jordle",
                    FPPredicate::OLT => "jordlt",
                    FPPredicate::UEQ => "junoeq",
                    FPPredicate::UNE => "junone",
                    FPPredicate::UGE => "junoge",
                    FPPredicate::UGT => "junogt",
                    FPPredicate::ULE => "junole",
                    FPPredicate::ULT => "junolt",
                    _ => todo!(),
                };
                let label_id = self.alloc_id();
                let dest = self.get_or_else(&instr.dest.to_string(), |pool| {
                    pool.push_primitive(&instr.dest.to_string(), InstructionSize::U8, false)
                });
                let id = self.alloc_id();
                let true_dest_name = format!("__{label_id}_fcmp_true{}", id);
                let false_dest_name = format!("__{label_id}_fcmp_false{}", id);
                let end_dest_name = format!("__{label_id}_fcmp_end{}", id);
                let true_dest = self.pool().label(&function_name, &true_dest_name);
                let false_dest = self.pool().label(&function_name, &false_dest_name);
                let end_dest = self.pool().label(&function_name, &end_dest_name);

                writeln!(self.current_function.body, "    fcmp{} {} {}", size, a, b)?;
                writeln!(
                    self.current_function.body,
                    "    {}{} {}",
                    predicate,
                    true_dest.size(),
                    true_dest
                )?;
                writeln!(
                    self.current_function.body,
                    "    jmp{} {}",
                    false_dest.size(),
                    false_dest
                )?;
                writeln!(self.current_function.body, "{}", true_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} $1",
                    dest.size(),
                    dest
                )?;
                writeln!(
                    self.current_function.body,
                    "    jmp{} {}",
                    end_dest.size(),
                    end_dest
                )?;
                writeln!(self.current_function.body, "{}", false_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} rz",
                    dest.size(),
                    dest
                )?;
                writeln!(self.current_function.body, "{}", end_dest)?;
            }

            Instruction::Select(instr) => {
                let cond = self.parse_operand(None, &instr.condition, true)?;
                let true_val = self.parse_operand(None, &instr.true_value, false)?;
                let false_val = self.parse_operand(None, &instr.false_value, false)?;
                assert_eq!(true_val.size(), false_val.size()); // sanity check
                let types = &self.module.types.to_owned();
                let dest = self.get_or_else(
                    &instr.dest.to_string(),
                    |pool| {
                        Ssa::push(
                            &instr.false_value.get_type(types),
                            instr.dest.to_string(),
                            types,
                            pool,
                        )
                    }, //pool.push_primitive(&instr.dest.to_string(), true_val.size(), false)
                );

                let id = self.alloc_id();
                let true_dest_name = format!("__select_true{}", id);
                let false_dest_name = format!("__select_false{}", id);
                let end_dest_name = format!("__select_end{}", id);
                let true_dest = self.pool().label(&function_name, &true_dest_name);
                let false_dest = self.pool().label(&function_name, &false_dest_name);
                let end_dest = self.pool().label(&function_name, &end_dest_name);

                writeln!(
                    self.current_function.body,
                    "    cmp{} {} rz",
                    cond.size(),
                    cond
                )?;
                writeln!(
                    self.current_function.body,
                    "    jne{} {}",
                    true_dest.size(),
                    true_dest
                )?;
                writeln!(
                    self.current_function.body,
                    "    jmp{} {}",
                    false_dest.size(),
                    false_dest
                )?;
                writeln!(self.current_function.body, "{}", true_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dest.size(),
                    dest,
                    true_val
                )?;
                writeln!(
                    self.current_function.body,
                    "    jmp{} {}",
                    end_dest.size(),
                    end_dest
                )?;
                writeln!(self.current_function.body, "{}", false_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dest.size(),
                    dest,
                    false_val
                )?;
                writeln!(
                    self.current_function.body,
                    "    jmp{} {}",
                    end_dest.size(),
                    end_dest
                )?;
                writeln!(self.current_function.body, "{}", end_dest)?;
            }
            Instruction::ZExt(instr) => {
                let src = self.parse_operand(None, &instr.operand, false)?;
                let to_type = op_size(&instr.to_type);
                let types = &self.module.types.to_owned();
                let dst = self.get_or_else(&instr.dest.to_string(), |pool| {
                    Ssa::push(&instr.to_type, instr.dest.to_string(), types, pool)
                });

                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    to_type, dst, src,
                )?;
            }
            Instruction::SExt(instr) => {
                let src = self.parse_operand(None, &instr.operand, false)?;
                let to_type = op_size(&instr.to_type);
                let types = &self.module.types.to_owned();
                let dst = self.get_or_else(&instr.dest.to_string(), |pool| {
                    Ssa::push(&instr.to_type, instr.dest.to_string(), types, pool)
                });

                writeln!(
                    self.current_function.body,
                    "    sext{} {} {}",
                    to_type, dst, src,
                )?;
            }
            Instruction::Trunc(instr) => {
                let src = self.parse_operand(None, &instr.operand, false)?;
                let types = &self.module.types.to_owned();
                let dst = self.get_or_else(&instr.dest.to_string(), |pool| {
                    Ssa::push(&instr.to_type, instr.dest.to_string(), types, pool)
                });

                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dst.size(),
                    dst,
                    src,
                )?;
            }
            Instruction::BitCast(instr) => {
                let src = self.parse_operand(None, &instr.operand, false)?;
                let dst = Ssa::push(
                    &instr.to_type,
                    instr.dest.to_string(),
                    &self.module.types.to_owned(),
                    self.pool(),
                );

                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dst.size(),
                    dst,
                    src,
                )?;
            }
            Instruction::GetElementPtr(instr) => {
                let indices: Vec<_> = instr
                    .indices
                    .iter()
                    .map(|ind| self.parse_operand(None, ind, true).unwrap())
                    .collect();

                let src = self.parse_operand(None, &instr.address, false)?;
                let _dst = self.get_element_ptr(&instr.dest.to_string(), src, indices)?;
            }
            Instruction::Phi(instr) => {
                // "which of these labels did we just come from?"
                let label_end_id = self.alloc_id();
                let types = self.module.types.to_owned();
                let dest = self.get_or_else(&instr.dest.to_string(), |pool| {
                    Ssa::push(&instr.to_type, instr.dest.to_string(), &types, pool)
                });
                let end = self
                    .pool()
                    .label(&function_name, &format!("%__{}_phi_end", label_end_id));
                let mut yesses = vec![];
                for (val, label) in instr.incoming_values.iter() {
                    let val = self.parse_operand(None, val, false)?;
                    let label = self.pool().label(&function_name, &label.to_string());
                    let yes_id = self.alloc_id();
                    let yes = self
                        .pool()
                        .label(&function_name, &format!("__{}_phi_{}", yes_id, label));
                    yesses.push((yes.clone(), val.clone()));
                    writeln!(
                        self.current_function.body,
                        "    cmp{} {} {}",
                        last_block.size(),
                        last_block,
                        label
                    )?;
                    writeln!(self.current_function.body, "    jeq{} {}", yes.size(), yes)?;
                }
                writeln!(self.current_function.body, "    und")?;
                for (yes, val) in yesses.iter() {
                    writeln!(self.current_function.body, "{}", yes)?;
                    writeln!(
                        self.current_function.body,
                        "    mov{} {} {}",
                        dest.size(),
                        dest,
                        val
                    )?;
                    writeln!(self.current_function.body, "    jmp{} {}", end.size(), end)?;
                }

                writeln!(self.current_function.body, "{}", end)?;
            }
            Instruction::Call(instr) => {
                let func = if instr.function.is_right() {
                    let func = instr.function.as_ref().unwrap_right();
                    self.parse_operand(None, func, false)?
                } else {
                    let func_name = self.current_function.name.to_owned();
                    let id = self.alloc_id();
                    let ssa = Rc::new(Ssa::StaticFunction {
                        name: format!("%{}_inline_asm_{}", rustc_demangle::demangle(&func_name).as_str(), id),
                        return_type: Type::VoidType,
                    });
                    self.pool().insert(ssa.clone());
                    ssa
                };

                let mut args = vec![];
                for (arg, _) in instr.arguments.iter() {
                    if let Operand::MetadataOperand = arg {
                    } else {
                        args.push(self.parse_operand(None, arg, true)?);
                    }
                }
                let dest = if let Ssa::StaticFunction { return_type, .. } = func.as_ref() {
                    if let Type::VoidType = return_type {
                        None
                    } else {
                        instr.dest.as_ref().map(|dest| {
                            Ssa::push(
                                return_type,
                                dest.to_string(),
                                &self.module.types.to_owned(),
                                self.pool(),
                            )
                        })
                    }
                } else if let Ssa::Function { return_type, .. } = func.as_ref() {
                    if let Type::VoidType = return_type {
                        None
                    } else {
                        instr.dest.as_ref().map(|dest| {
                            Ssa::push(
                                return_type,
                                dest.to_string(),
                                &self.module.types.to_owned(),
                                self.pool(),
                            )
                        })
                    }
                } else if let Ssa::Pointer { pointee_type, .. }
                | Ssa::StaticPointer { pointee_type, .. } = func.as_ref()
                {
                    if let Type::FuncType { result_type, .. } = pointee_type {
                        if let Type::VoidType = result_type.as_ref().to_owned() {
                            None
                        } else {
                            instr.dest.as_ref().map(|dest| {
                                Ssa::push(
                                    result_type,
                                    dest.to_string(),
                                    &self.module.types.to_owned(),
                                    self.pool(),
                                )
                            })
                        }
                    } else {
                        todo!()
                    }
                } else {
                    unreachable!("{:?}", func.as_ref())
                };

                for (arg, reg) in args.iter().zip(
                    [
                        Register::Rg,
                        Register::Rh,
                        Register::Ri,
                        Register::Rj,
                        Register::Rk,
                        Register::Rl,
                    ][..args.len().min(6)]
                        .iter(),
                ) {
                    writeln!(
                        self.current_function.body,
                        "    mov{} {} {}",
                        arg.size(),
                        reg.asm_repr(),
                        arg
                    )?;
                }
                if args.len() > 6 {
                    for arg in args[6..].iter() {
                        writeln!(self.current_function.body, "    push{} {}", arg.size(), arg)?;
                    }
                }
                writeln!(
                    self.current_function.body,
                    "    call{} {}",
                    func.size(),
                    func
                )?;
                if let Some(dest) = dest {
                    writeln!(
                        self.current_function.body,
                        "    mov{} {} ra",
                        dest.size(),
                        dest
                    )?;
                }
            }
            Instruction::InsertValue(instr) => {
                let val = self.parse_operand(None, &instr.element, false)?;
                let agg = self.parse_operand(None, &instr.aggregate, true)?;
                assert_eq!(
                    instr.indices.len(),
                    1,
                    "todo: multiple indices for insertvalue"
                );
                // let indices = instr
                // .indices
                // .iter()
                // .map(|index| {
                //     Rc::new(Ssa::Constant {
                //         name: format!(
                //             "index_{}",
                //             self.alloc_id()
                //         ),
                //         value: Literal::Dword((*index).into()),
                //         signed: false,
                //     })
                // })
                // .collect::<Vec<_>>();

                let dst = agg.duplicate(&instr.dest.to_string());
                let dst = self.pool().push(dst);
                let id = self.alloc_id();

                let ptr = if let Ssa::Composite { elements, .. } = dst.as_ref() {
                    let types = &self.module.types.to_owned();
                    let ptr = self.pool().push_pointer(
                        &format!("insertelement_{}_ptr_{}", agg.name(), id),
                        instr.element.get_type(types).as_ref().to_owned(),
                    );
                    writeln!(
                        self.current_function.body,
                        "    mov{} {} {}",
                        ptr.size(),
                        ptr,
                        elements[instr.indices[0] as usize].name()
                    )?;
                    ptr
                } else if let Ssa::Pointer { .. } = dst.as_ref() {
                    // this is technically a bug, but it's a convenient bug
                    dst
                } else {
                    unreachable!("{:?}", dst.as_ref())
                };
                let tmp = self
                    .pool()
                    .get_unused_register("tmp", InstructionSize::U64)
                    .unwrap();
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    tmp.size(),
                    tmp,
                    ptr
                )?;
                writeln!(
                    self.current_function.body,
                    "    mov{} [{}] {}",
                    val.size(),
                    tmp,
                    val
                )?;
                self.pool().take_back(tmp);
            }
            Instruction::ExtractValue(instr) => {
                let agg = self.parse_operand(None, &instr.aggregate, false)?;
                assert_eq!(
                    instr.indices.len(),
                    1,
                    "todo: multiple indices for extractvalue"
                );
                let (elem, elem_type) = if let Ssa::Composite {
                    elements,
                    element_types,
                    ..
                } = agg.as_ref()
                {
                    (
                        elements[instr.indices[0] as usize].clone(),
                        element_types[instr.indices[0] as usize].clone(),
                    )
                } else if let Ssa::StaticComposite {
                    elements,
                    element_types,
                    ..
                } = agg.as_ref()
                {
                    (
                        elements[instr.indices[0] as usize].clone(),
                        element_types[instr.indices[0] as usize].clone(),
                    )
                } else {
                    unreachable!("{:?}", agg.as_ref())
                };
                let types = &self.module.types.to_owned();
                let dest = Ssa::push(&elem_type, instr.dest.to_string(), types, self.pool());
                if let Some(stack_offset) = elem.stack_offset() {
                    let tmp = self.pool().get_unused_register("tmp", elem.size()).unwrap();
                    writeln!(
                        self.current_function.body,
                        "    mov{} {} bp",
                        tmp.size(),
                        tmp
                    )?;
                    writeln!(
                        self.current_function.body,
                        "    sub{} {} ${}",
                        tmp.size(),
                        tmp,
                        stack_offset
                    )?;

                    writeln!(
                        self.current_function.body,
                        "    mov{} {} [{}]",
                        dest.size(),
                        dest,
                        tmp
                    )?;
                    self.pool().take_back(tmp);
                } else {
                    let tmp = self.pool().get_unused_register("tmp", elem.size()).unwrap();
                    writeln!(
                        self.current_function.body,
                        "    mov{} {} {}",
                        tmp.size(),
                        tmp,
                        elem.name()
                    )?;
                    writeln!(
                        self.current_function.body,
                        "    mov{} {} [{}]",
                        dest.size(),
                        dest,
                        tmp
                    )?;
                    self.pool().take_back(tmp);
                }
            }
            Instruction::PtrToInt(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let dst = self.get_or_else(&instr.dest.to_string(), |pool| {
                    pool.push_primitive(&instr.dest.to_string(), op_size(&instr.to_type), false)
                });
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dst.size(),
                    dst,
                    src
                )?;
            }
            Instruction::IntToPtr(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let dst = self.get_or_else(&instr.dest.to_string(), |pool| {
                    pool.push_primitive(&instr.dest.to_string(), op_size(&instr.to_type), false)
                });
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dst.size(),
                    dst,
                    src
                )?;
            }
            Instruction::SIToFP(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let dst = self.get_or_else(&instr.dest.to_string(), |pool| {
                    pool.push_primitive(&instr.dest.to_string(), op_size(&instr.to_type), false)
                });
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dst.size(),
                    dst,
                    src
                )?;
            }
            Instruction::UIToFP(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let dst = self.get_or_else(&instr.dest.to_string(), |pool| {
                    pool.push_primitive(&instr.dest.to_string(), op_size(&instr.to_type), false)
                });
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dst.size(),
                    dst,
                    src
                )?;
            }
            Instruction::Freeze(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let types = &self.module.types.to_owned();
                let dst = self.get_or_else(&instr.dest.to_string(), |pool| {
                    pool.push_primitive(
                        &instr.dest.to_string(),
                        op_size(&instr.operand.get_type(types)),
                        false,
                    )
                });
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dst.size(),
                    dst,
                    src
                )?;
            }

            x => {
                panic!("UNKNOWN INSTRUCTION:    {}", x)
            }
        }
        Ok(())
    }
}
