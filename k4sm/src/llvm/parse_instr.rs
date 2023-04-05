use std::{error::Error, fmt::Write, rc::Rc, sync::atomic::Ordering};

use k4s::{InstructionSize, Literal};
use llvm_ir::{Instruction, IntPredicate};

use crate::llvm::{
    op_size,
    ssa::{Register, Ssa},
};

use super::Parser;

impl Parser {
    pub fn parse_instr(&mut self, instr: &Instruction) -> Result<(), Box<dyn Error>> {
        macro_rules! match_arith {
            ($instr:expr, $mn:literal) => {{
                let a = self.parse_operand(None, &$instr.operand0, true)?;
                let b = self.parse_operand(None, &$instr.operand1, true)?;
                assert_eq!(a.size(), b.size());
                let dst = self.get_or_push_primitive(
                    &$instr.dest.to_string(),
                    Literal::default_for_size(a.size()),
                );

                writeln!(&mut self.current_function.body, "; {}", $instr)?;
                writeln!(
                    &mut self.current_function.body,
                    "    mov{} {} {}",
                    dst.size(),
                    dst.display(),
                    a.display()
                )?;
                writeln!(
                    &mut self.current_function.body,
                    concat!("    ", $mn, "{} {} {}"),
                    dst.size(),
                    dst.display(),
                    b.display()
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
                let off = self.pool().stack_size;
                let ptr = self.pool().push_pointer(&instr.dest.to_string(), ssa);
                let tmp = self
                    .pool()
                    .get_unused_register("tmp", InstructionSize::Qword)
                    .unwrap();
                writeln!(self.current_function.body, "    mov q {} bp", tmp)?;
                writeln!(self.current_function.body, "    sub q {} ${}", tmp, off)?;
                writeln!(self.current_function.body, "    mov q {} {}", ptr, tmp)?;
                self.pool().take_back("tmp", tmp);
            }
            Instruction::Store(instr) => {
                let dst = self.parse_operand(None, &instr.address, true)?;
                let src = self.parse_operand(None, &instr.value, true)?;
                match (src.stack_offset(), dst.stack_offset()) {
                    (Some(_), Some(_)) => {
                        let tmp1 = self
                            .pool()
                            .get_unused_register("tmp1", InstructionSize::Qword)
                            .unwrap();
                        writeln!(self.current_function.body, "; [{}] <= {}", dst, src)?;
                        writeln!(self.current_function.body, "    mov q {} {}", tmp1, dst,)?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            InstructionSize::Qword,
                            tmp1,
                            src
                        )?;
                        self.pool().take_back("tmp1", tmp1);
                    }
                    (Some(_), None) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            InstructionSize::Qword,
                            dst,
                            src
                        )?;
                    }
                    (None, Some(_)) => {
                        let tmp1 = self
                            .pool()
                            .get_unused_register("tmp1", InstructionSize::Qword)
                            .unwrap();
                        writeln!(self.current_function.body, "; [{}] <= {}", dst, src)?;
                        writeln!(self.current_function.body, "    mov q {} {}", tmp1, dst,)?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            InstructionSize::Qword,
                            tmp1,
                            src
                        )?;
                        self.pool().take_back("tmp1", tmp1);
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
                let dst = self.get_or_push_primitive(
                    &instr.dest.to_string(),
                    Literal::default_for_size(src.size()),
                );

                let align = InstructionSize::from_n_bytes(instr.alignment);
                match (src.stack_offset(), dst.stack_offset()) {
                    (Some(src_off), Some(dst_off)) => {
                        let tmp = self
                            .pool()
                            .get_unused_register("tmp", InstructionSize::Qword)
                            .unwrap();
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [-{}+bp]",
                            InstructionSize::Qword,
                            tmp,
                            src_off
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} [-{}+bp] [{}]",
                            InstructionSize::Qword,
                            dst_off,
                            tmp
                        )?;
                        self.pool().take_back("tmp", tmp);
                    }
                    (Some(src_off), None) => {
                        let tmp = self
                            .pool()
                            .get_unused_register("tmp", InstructionSize::Qword)
                            .unwrap();
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [-{}+bp]",
                            InstructionSize::Qword,
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
                        self.pool().take_back("tmp", tmp);
                    }
                    (None, Some(dst_off)) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} [-{}+bp] [{}]",
                            align, dst_off, src
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
            Instruction::Shl(instr) => match_arith!(instr, "shl"),
            Instruction::LShr(instr) => match_arith!(instr, "shr"),
            Instruction::Or(instr) => match_arith!(instr, "or"),
            Instruction::And(instr) => match_arith!(instr, "and"),
            Instruction::Xor(instr) => match_arith!(instr, "xor"),

            Instruction::ICmp(instr) => {
                let a = self.parse_operand(None, &instr.operand0, true)?;
                let b = self.parse_operand(None, &instr.operand1, true)?;
                let size = std::cmp::max(a.size(), b.size());
                let predicate = match instr.predicate {
                    IntPredicate::EQ => "jeq",
                    IntPredicate::ULT | IntPredicate::SLT => "jlt",
                    IntPredicate::UGT | IntPredicate::SGT => "jgt",
                    IntPredicate::NE => "jne",
                    _ => todo!(),
                };
                let comparison = match instr.predicate {
                    IntPredicate::SGE | IntPredicate::SLE => "scmp",
                    _ => "cmp",
                };
                let label_id = self.current_function.label_count;
                let dest = self.get_or_push_primitive(
                    &instr.dest.to_string(),
                    Literal::default_for_size(InstructionSize::Byte),
                );
                let id = self.anon_datas.fetch_add(1, Ordering::SeqCst);
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
                    "    {} q {}",
                    predicate, true_dest
                )?;
                writeln!(self.current_function.body, "    jmp q {}", false_dest)?;
                writeln!(self.current_function.body, "{}", true_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} $1",
                    dest.size(),
                    dest
                )?;
                writeln!(self.current_function.body, "    jmp q {}", end_dest)?;
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
                let dest = self.get_or_push_primitive(
                    &instr.dest.to_string(),
                    Literal::default_for_size(InstructionSize::Byte),
                );

                let id = self.anon_datas.fetch_add(1, Ordering::SeqCst);
                let true_dest_name = format!("__select_true{}", id);
                let false_dest_name = format!("__select_true{}", id);
                let end_dest_name = format!("__select_end{}", id);
                let true_dest = self.pool().label(&function_name, &true_dest_name);
                let false_dest = self.pool().label(&function_name, &false_dest_name);
                let end_dest = self.pool().label(&function_name, &end_dest_name);

                writeln!(self.current_function.body, "    cmp b {} rz", cond)?;
                writeln!(self.current_function.body, "    jne q {}", true_dest)?;
                writeln!(self.current_function.body, "    jmp q {}", false_dest)?;
                writeln!(self.current_function.body, "{}", true_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dest.size(),
                    dest,
                    true_val
                )?;
                writeln!(self.current_function.body, "    jmp q {}", end_dest)?;
                writeln!(self.current_function.body, "{}", false_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dest.size(),
                    dest,
                    false_val
                )?;
                writeln!(self.current_function.body, "    jmp q {}", end_dest)?;
                writeln!(self.current_function.body, "{}", end_dest)?;
            }
            Instruction::ZExt(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let to_type = op_size(&instr.to_type);
                let dst = self.get_or_push_primitive(
                    &instr.dest.to_string(),
                    Literal::default_for_size(to_type),
                );

                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    to_type, dst, src,
                )?;
            }
            Instruction::Trunc(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let to_type = op_size(&instr.to_type);
                let dst = self.get_or_push_primitive(
                    &instr.dest.to_string(),
                    Literal::default_for_size(to_type),
                );

                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    to_type, dst, src,
                )?;
            }
            Instruction::BitCast(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let to_type = op_size(&instr.to_type);
                let dst = self.get_or_push_primitive(
                    &instr.dest.to_string(),
                    Literal::default_for_size(to_type),
                );

                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    to_type, dst, src,
                )?;
            }
            Instruction::GetElementPtr(instr) => {
                let dst = self.get_or_push_primitive(
                    &instr.dest.to_string(),
                    Literal::default_for_size(InstructionSize::Qword),
                );
                let indices: Vec<_> = instr
                    .indices
                    .iter()
                    .map(|ind| self.parse_operand(None, ind, true).unwrap())
                    .collect();

                let src = self.parse_operand(None, &instr.address, true)?;
                let offset = self.get_element_ptr(src, indices)?;

                writeln!(self.current_function.body, "    mov q {} bp", dst)?;
                writeln!(self.current_function.body, "    sub q {} {}", dst, offset)?;
            }
            Instruction::Phi(instr) => {
                // "which of these labels did we just come from?"
                let label_id = self.current_function.label_count;
                let dest = self.get_or_push_primitive(
                    &instr.dest.to_string(),
                    Literal::default_for_size(op_size(&instr.to_type)),
                );
                let end = self
                    .pool()
                    .label(&function_name, &format!("%__{}_phi_end", label_id));
                let mut yesses = vec![];
                for (val, label) in instr.incoming_values.iter() {
                    let val = self.parse_operand(None, val, false)?;
                    let label = self.pool().label(&function_name, &label.to_string());
                    let yes = self
                        .pool()
                        .label(&function_name, &format!("__{}_phi_{}", label_id, label));
                    yesses.push((yes.clone(), val.clone()));
                    writeln!(
                        self.current_function.body,
                        "    cmp q {} {}",
                        last_block, label
                    )?;
                    writeln!(self.current_function.body, "    jeq q {}", yes)?;
                }
                writeln!(self.current_function.body, "    und")?;
                for (yes, val) in yesses.iter() {
                    writeln!(self.current_function.body, "{}", yes)?;
                    writeln!(self.current_function.body, "    mov q {} {}", dest, val)?;
                    writeln!(self.current_function.body, "    jmp q {}", end)?;
                }

                writeln!(self.current_function.body, "{}", end)?;

                self.current_function.label_count += 1;
            }
            Instruction::Call(instr) => {
                let func = instr.function.as_ref().unwrap_right();
                let func = self.parse_operand(None, func, false)?;
                let mut args = vec![];
                for (arg, _) in instr.arguments.iter() {
                    args.push(self.parse_operand(None, arg, true)?);
                }
                let dest = instr.dest.as_ref().map(|dest| {
                    self.get_or_push_primitive(
                        &dest.to_string(),
                        Literal::default_for_size(func.size()),
                    )
                });
                for (arg, reg) in args.iter().zip(
                    [
                        Register::Rg,
                        Register::Rh,
                        Register::Ri,
                        Register::Rj,
                        Register::Rk,
                        Register::Rl,
                    ][..args.len()]
                        .iter(),
                ) {
                    writeln!(
                        self.current_function.body,
                        "    mov{} {} {}",
                        arg.size(),
                        reg.display(),
                        arg
                    )?;
                }
                writeln!(self.current_function.body, "    call q {}", func)?;
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
                let indices = instr
                    .indices
                    .iter()
                    .map(|index| {
                        Rc::new(Ssa::Constant {
                            name: format!(
                                "index_{}",
                                self.anon_datas.fetch_add(1, Ordering::SeqCst)
                            ),
                            value: Literal::Dword((*index).into()),
                            signed: false,
                        })
                    })
                    .collect::<Vec<_>>();
                let agg = self.parse_operand(None, &instr.aggregate, true)?;
                let dst = agg.duplicate(&instr.dest.to_string());

                self.pool().insert(dst.clone());
                let ptr = self.get_element_ptr(dst, indices)?;
                let tmp = self
                    .pool()
                    .get_unused_register("tmp", InstructionSize::Qword)
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
                self.pool().take_back(&tmp.name(), tmp);
            }

            x => {
                panic!("UNKNOWN INSTRUCTION:    {}", x)
            }
        }
        Ok(())
    }
}
