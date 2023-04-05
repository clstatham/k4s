// #![allow(unused_variables)]

use std::{collections::HashMap, error::Error, fmt::Write, path::Path};

use k4s::{InstructionSize, Literal};
use llvm_ir::{
    terminator::{Br, CondBr, Ret},
    Constant, Instruction, IntPredicate, Module, Name, Operand, Terminator, Type,
};

use crate::llvm::ssa::{CompositeTypeStorage, Register};

use self::{
    regpool::RegPool,
    ssa::{CompositeType, Ssa, Storage},
};

pub mod regpool;
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
        Type::ArrayType {
            element_type,
            num_elements,
        } => todo!(),
        Type::StructType { .. } => InstructionSize::Unsized,
        Type::NamedStructType { .. } => InstructionSize::Unsized,
        _ => todo!(),
    }
}

#[derive(Default)]
pub struct Function {
    name: String,

    prologue: String,
    body: String,
    epilogue: String,

    pool: RegPool,
    last_block: Option<Ssa>,

    label_count: usize,
}

pub struct Parser {
    module: Module,
    output: String,

    current_function: Function,
}

impl Parser {
    pub fn new(bc_path: impl AsRef<Path>) -> Self {
        Self {
            module: Module::from_bc_path(bc_path).unwrap(),
            output: String::new(),
            current_function: Function::default(),
        }
    }

    pub fn function_name(&self) -> String {
        self.current_function.name.clone()
    }

    pub fn pool(&mut self) -> &mut RegPool {
        &mut self.current_function.pool
    }

    fn parse_instr(&mut self, instr: &Instruction) -> Result<(), Box<dyn Error>> {
        macro_rules! match_arith {
            ($instr:expr, $mn:literal) => {{
                let a = self.parse_operand(None, &$instr.operand0, true)?;
                let b = self.parse_operand(None, &$instr.operand1, true)?;
                assert_eq!(a.size, b.size);
                let dst = self.get_or_push_literal(
                    &$instr.dest.to_string(),
                    Literal::default_for_size(a.size),
                );

                writeln!(&mut self.current_function.body, "; {}", $instr)?;
                writeln!(
                    &mut self.current_function.body,
                    "    mov{} {} {}",
                    dst.size,
                    dst.storage.display(),
                    a.storage.display()
                )?;
                writeln!(
                    &mut self.current_function.body,
                    concat!("    ", $mn, "{} {} {}"),
                    dst.size,
                    dst.storage.display(),
                    b.storage.display()
                )?;
                // pool.reinsert(a);
                // pool.reinsert(b);
            }};
        }
        let function_name = self.function_name();
        let last_block = self.current_function.last_block.as_ref().unwrap().clone();
        writeln!(self.current_function.body, "; {}", instr)?;
        match instr {
            Instruction::Alloca(instr) => {
                // this is a pointer
                let count = self.parse_operand(None, &instr.num_elements, false)?;
                let count = if let Storage::Constant { value, .. } = count.storage {
                    value.as_qword().get() as usize
                } else {
                    todo!("{:?}", count.storage)
                };
                assert_eq!(count, 1);

                let storage =
                    CompositeTypeStorage::parse(&instr.allocated_type, &self.module.types);
                // match &*instr.allocated_type {
                let pointee = self
                    .pool()
                    .push_composite(&format!("{}_pointee", &instr.dest.to_string()), storage);
                let off = pointee.storage.stack_offset().unwrap();
                let ptr = self
                    .pool()
                    .push_pointer(&instr.dest.to_string(), pointee.into());
                let tmp = self
                    .pool()
                    .get_unused("alloca_tmp", InstructionSize::Qword)
                    .unwrap();
                writeln!(
                    self.current_function.body,
                    "    mov q {} bp",
                    tmp.storage.display()
                )?;
                writeln!(
                    self.current_function.body,
                    "    sub q {} ${}",
                    tmp.storage.display(),
                    off
                )?;
                writeln!(
                    self.current_function.body,
                    "    mov q {} {}",
                    ptr.storage.display(),
                    tmp.storage.display()
                )?;
                self.pool().take_back(tmp);

                // match ptr.storage {
                //     Storage::StackLocal { off, .. } => {
                //         let tmp = self.pool().get_unused("alloca_tmp", InstructionSize::Qword).unwrap();
                //         writeln!(self.current_function.body, "    mov q {} bp", tmp.storage.display())?;
                //         writeln!(self.current_function.body, "    sub q {} ${}", tmp.storage.display(), off)?;
                //         let val = self.push_stack(&instr.dest.to_string(), InstructionSize::Qword, 1);
                //         writeln!(self.current_function.body, "    mov q {} {}", val.storage.display(), tmp.storage.display())?;
                //         self.pool().take_back(tmp);
                //     }
                //     Storage::StackLocalComposite { off, .. } => {
                //         let tmp = self.pool().get_unused("alloca_tmp", InstructionSize::Qword).unwrap();
                //         writeln!(self.current_function.body, "    mov q {} bp", tmp.storage.display())?;
                //         writeln!(self.current_function.body, "    sub q {} ${}", tmp.storage.display(), off)?;
                //         let val = self.push_struct_stack(&instr.dest.to_string(), ptr.storage);
                //         writeln!(self.current_function.body, "    mov q {} {}", val.storage.display(), tmp.storage.display())?;
                //         self.pool().take_back(tmp);
                //     }
                // _ => unreachable!()
                // }
                // dbg!(size, count);

                // last_dst = Some(ssa.clone());
            }
            Instruction::Store(instr) => {
                let dst = self.parse_operand(None, &instr.address, true)?;
                let src = self.parse_operand(None, &instr.value, true)?;
                match (src.storage.stack_offset(), dst.storage.stack_offset()) {
                    (Some(_), Some(_)) => {
                        let tmp1 = self
                            .pool()
                            .get_unused("tmp1", InstructionSize::Qword)
                            .unwrap();
                        writeln!(
                            self.current_function.body,
                            "; [{}] <= {}",
                            dst.storage.display(), src.storage.display()
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov q {} {}",
                            tmp1.storage.display(),
                            dst.storage.display(),
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            InstructionSize::Qword,
                            tmp1.storage.display(),
                            src.storage.display()
                        )?;
                        self.pool().take_back(tmp1);
                    }
                    (Some(_), None) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            InstructionSize::Qword,
                            dst.storage.display(),
                            src.storage.display()
                        )?;
                    }
                    (None, Some(_)) => {
                        let tmp1 = self
                            .pool()
                            .get_unused(&format!("{}_ptr_tmp1", dst.name), InstructionSize::Qword)
                            .unwrap();
                        writeln!(
                            self.current_function.body,
                            "; [{}] <= {}",
                            dst.storage.display(), src.storage.display()
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov q {} {}",
                            tmp1.storage.display(),
                            dst.storage.display(),
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            InstructionSize::Qword,
                            tmp1.storage.display(),
                            src.storage.display()
                        )?;
                        // } else {
                        //     unreachable!()
                        // }

                        self.pool().take_back(tmp1);
                        // self.pool().take_back(tmp2);
                    }
                    (None, None) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            dst.size,
                            dst.storage.display(),
                            src.storage.display()
                        )?;
                    }
                }
                // pool.reinsert(tmp_dst);
            }
            Instruction::Load(instr) => {
                let src = self.parse_operand(None, &instr.address, true)?;
                let dst = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(src.size),
                );
                // let size = std::cmp::max(src.size, dst.size);

                let align = InstructionSize::from_n_bytes(instr.alignment);
                match (src.storage.stack_offset(), dst.storage.stack_offset()) {
                    (Some(src_off), Some(dst_off)) => {
                        let tmp = self
                            .pool()
                            .get_unused("tmp1", InstructionSize::Qword)
                            .unwrap();
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [-{}+bp]",
                            InstructionSize::Qword,
                            tmp.storage.display(),
                            src_off
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} [-{}+bp] [{}]",
                            InstructionSize::Qword,
                            dst_off,
                            tmp.storage.display()
                        )?;
                        self.pool().take_back(tmp);
                    }
                    (Some(src_off), None) => {
                        let tmp = self
                            .pool()
                            .get_unused("tmp", InstructionSize::Qword)
                            .unwrap();
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [-{}+bp]",
                            InstructionSize::Qword,
                            tmp.storage.display(),
                            src_off
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [{}]",
                            dst.size,
                            dst.storage.display(),
                            tmp.storage.display()
                        )?;
                        self.pool().take_back(tmp);
                    }
                    (None, Some(dst_off)) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} [-{}+bp] [{}]",
                            align,
                            dst_off,
                            src.storage.display()
                        )?;
                    }
                    (None, None) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [{}]",
                            dst.size,
                            dst.storage.display(),
                            src.storage.display()
                        )?;
                    }
                }
            }
            Instruction::Add(instr) => match_arith!(instr, "add"),
            Instruction::Sub(instr) => match_arith!(instr, "sub"),
            Instruction::Mul(instr) => match_arith!(instr, "mul"),
            Instruction::Shl(instr) => match_arith!(instr, "shl"),
            Instruction::ICmp(instr) => {
                let a = self.parse_operand(None, &instr.operand0, true)?;
                let b = self.parse_operand(None, &instr.operand1, true)?;
                let size = std::cmp::max(a.size, b.size);
                let predicate = match instr.predicate {
                    IntPredicate::EQ => "jeq",
                    IntPredicate::ULT => "jlt",
                    IntPredicate::NE => "jne",
                    _ => todo!(),
                };
                let label_id = self.current_function.label_count;
                // assert_eq!(a.storage.size(), b.storage.size());
                let dest = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(InstructionSize::Byte),
                );
                let true_dest_name = format!("__{label_id}_cmp_true",);
                let false_dest_name = format!("__{label_id}_cmp_false",);
                let end_dest_name = format!("__{label_id}_cmp_end",);
                let true_dest = self.pool().label(&function_name, &true_dest_name);
                let false_dest = self.pool().label(&function_name, &false_dest_name);
                let end_dest = self.pool().label(&function_name, &end_dest_name);

                writeln!(
                    self.current_function.body,
                    "    cmp{} {} {}",
                    size,
                    a.storage.display(),
                    b.storage.display()
                )?;
                writeln!(
                    self.current_function.body,
                    "    {} q {}",
                    predicate,
                    true_dest.storage.display()
                )?;
                writeln!(
                    self.current_function.body,
                    "    jmp q {}",
                    false_dest.storage.display()
                )?;
                writeln!(
                    self.current_function.body,
                    "{}",
                    true_dest.storage.display()
                )?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} $1",
                    dest.size,
                    dest.storage.display()
                )?;
                writeln!(
                    self.current_function.body,
                    "    jmp q {}",
                    end_dest.storage.display()
                )?;
                writeln!(
                    self.current_function.body,
                    "{}",
                    false_dest.storage.display()
                )?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} rz",
                    dest.size,
                    dest.storage.display()
                )?;
                writeln!(self.current_function.body, "{}", end_dest.storage.display())?;
            }
            Instruction::ZExt(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let to_type = op_size(&instr.to_type);
                let dst = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(to_type),
                );

                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    to_type,
                    dst.storage.display(),
                    src.storage.display(),
                )?;
            }
            Instruction::Trunc(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let to_type = op_size(&instr.to_type);
                let dst = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(to_type),
                );

                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    to_type,
                    dst.storage.display(),
                    src.storage.display(),
                )?;
            }
            Instruction::BitCast(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let to_type = op_size(&instr.to_type);
                let dst = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(to_type),
                );

                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    to_type,
                    dst.storage.display(),
                    src.storage.display(),
                )?;
            }
            Instruction::GetElementPtr(instr) => {
                let mut src = self.parse_operand(None, &instr.address, true)?;
                let dst = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(src.size),
                );
                let indices: Vec<Ssa> = instr
                    .indices
                    .iter()
                    .map(|ind| self.parse_operand(None, ind, true).unwrap())
                    .collect();
                
                let mut offset = 0;
                for index in indices.iter() {
                    let index = if let Storage::Constant { value, .. } = index.storage {
                        value.as_qword().get() as usize
                    } else if let Storage::Register { reg: Register::Rz } = index.storage {
                        0
                    } else {
                        todo!()
                    };
                    
                    match &src.storage {
                        Storage::Composite { stack_offset, ref typ_storage, .. } => {
                            // Literal::new(index.size(), typ_storage.byte_offset_of_element(index.as_qword().get() as usize).into())
                            offset = *stack_offset;
                            match typ_storage {
                                CompositeTypeStorage::Basic(_lit) => todo!(),
                                CompositeTypeStorage::Composite { elements } => {
                                    for elem in &elements[..index] {
                                        // writeln!(self.current_function.body, "    add q {} ${}", total.storage.display(), elem.size_in_bytes())?;
                                        offset -= elem.size_in_bytes();
                                    }
                                }
                            }
                        }
                        Storage::Pointer {
                            stack_offset: _,
                            pointee,
                            ..
                        } => {
                            
                            if index == 0 {
                                // fast path
                                // index of 0, we don't add anything
                            } else {
                                todo!()
                            }

                            src = *pointee.clone();
                        }
                        _ => {}
                    }
                }
                writeln!(self.current_function.body, "    mov q {} bp", dst.storage.display())?;
                writeln!(self.current_function.body, "    sub q {} ${}", dst.storage.display(), offset)?;
            }
            Instruction::Phi(instr) => {
                // "which of these labels did we just come from?"
                let label_id = self.current_function.label_count;
                let dest = self.get_or_push_literal(
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
                    let yes = self.pool().label(
                        &function_name,
                        &format!("__{}_phi_{}", label_id, label.name),
                    );
                    yesses.push((yes.clone(), val.clone()));
                    writeln!(
                        self.current_function.body,
                        "    cmp q {} {}",
                        last_block.storage.display(),
                        label.storage.display()
                    )?;
                    writeln!(
                        self.current_function.body,
                        "    jeq q {}",
                        yes.storage.display()
                    )?;
                }
                writeln!(self.current_function.body, "    hlt")?;
                for (yes, val) in yesses.iter() {
                    writeln!(self.current_function.body, "{}", yes.storage.display())?;
                    writeln!(
                        self.current_function.body,
                        "    mov q {} {}",
                        dest.storage.display(),
                        val.storage.display()
                    )?;
                    writeln!(
                        self.current_function.body,
                        "    jmp q {}",
                        end.storage.display()
                    )?;
                }

                writeln!(self.current_function.body, "{}", end.storage.display())?;

                self.current_function.label_count += 1;
            }
            Instruction::Call(instr) => {
                let func = instr.function.as_ref().unwrap_right();
                let func = self.parse_operand(None, func, false)?;
                let mut args = vec![];
                for (arg, _) in instr.arguments.iter() {
                    args.push(self.parse_operand(None, arg, true)?);
                }
                let dest = if let Some(ref dest) = instr.dest {
                    // assert_eq!(instr.return_attributes.len(), 1);
                    Some(self.get_or_push_literal(
                        &dest.to_string(),
                        Literal::default_for_size(func.size),
                    ))
                } else {
                    None
                };
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
                        arg.size,
                        reg.display(),
                        arg.storage.display()
                    )?;
                }
                writeln!(
                    self.current_function.body,
                    "    call q {}",
                    func.storage.display()
                )?;
                if let Some(dest) = dest {
                    writeln!(
                        self.current_function.body,
                        "    mov{} {} ra",
                        dest.size,
                        dest.storage.display()
                    )?;
                }
            }
            x => {
                panic!("UNKNOWN INSTRUCTION:    {}", x)
            }
        }
        Ok(())
    }

    pub fn parse_operand(
        &mut self,
        name: Option<Name>,
        op: &Operand,
        assert_exists: bool,
    ) -> Result<Ssa, Box<dyn Error>> {
        let function_name = self.current_function.name.clone();
        match op {
            Operand::ConstantOperand(con) => {
                let con = &**con;
                match con {
                    Constant::Int { bits, value } => {
                        if *value == 0 {
                            Ok(self.pool().rz(InstructionSize::from_n_bytes(bits / 8)))
                        } else {
                            let (value, signed) = (Literal::from_bits_value(*bits, *value), true);
                            Ok(Ssa::new(
                                Storage::Constant { value, signed },
                                value.size(),
                                "constant".to_owned(),
                            ))
                        }
                    }
                    Constant::GlobalReference { name, ty } => {
                        // println!("{}", name);
                        match &**ty {
                            Type::ArrayType { .. } => {
                                let name = format!("@{}", &name.to_string()[1..]);
                                // println!("{}", name);
                                // println!("{:?}", &name.as_bytes());
                                return Ok(self.pool().get(&name).unwrap());
                            }
                            Type::LabelType => return Ok(self.pool().label("", &name.to_string())),
                            Type::FuncType { .. } => {
                                return Ok(self.pool().label("", &name.to_string()))
                            }
                            Type::StructType { .. } => {
                                let storage = CompositeTypeStorage::parse(ty, &self.module.types);
                                dbg!(storage);
                                todo!()
                            }
                            Type::NamedStructType { name } => {
                                let struc = self.module.types.named_struct(name);
                                let storage =
                                    CompositeTypeStorage::parse(&struc, &self.module.types);
                                dbg!(storage);
                                todo!()
                            }
                            ty => {
                                todo!("{:?}", ty)
                            }
                        }
                    }
                    Constant::GetElementPtr(instr) => {
                        let dest = self.get_or_push_literal(
                            &format!("%{}_getelementptr", function_name),
                            Literal::default_for_size(InstructionSize::Qword),
                        );
                        self.parse_instr(&Instruction::GetElementPtr(
                            llvm_ir::instruction::GetElementPtr {
                                address: Operand::ConstantOperand(instr.address.clone()),
                                indices: instr
                                    .indices
                                    .iter()
                                    .map(|ind| Operand::ConstantOperand(ind.to_owned()))
                                    .collect(),
                                dest: dest.name[1..].into(),
                                in_bounds: instr.in_bounds,
                                debugloc: None,
                            },
                        ))?;
                        Ok(dest)
                    }
                    Constant::Array {
                        element_type,
                        elements,
                    } => {
                        assert_eq!(**element_type, Type::IntegerType { bits: 8 });
                        let mut data = vec![];
                        for elem in elements {
                            match &**elem {
                                Constant::Int { bits, value } => {
                                    assert_eq!(*bits, 8);
                                    data.push(*value as u8);
                                }
                                _ => todo!(),
                            }
                        }
                        let data_label = format!("@{}", &name.unwrap().to_string()[1..]);
                        // println!("{}", data_label);
                        // println!("{:?}", &data_label.as_bytes());
                        let ssa = Ssa::new(
                            Storage::Data {
                                label: data_label.clone(),
                                data: data.clone(),
                            },
                            InstructionSize::Qword,
                            data_label.to_owned(),
                        );
                        writeln!(
                            self.output,
                            "{} \"{}\"",
                            data_label,
                            std::str::from_utf8(&data).unwrap().trim_end()
                        )?;
                        self.current_function.pool.insert(ssa.clone());
                        // if let Some(ref mut pool) = self.current_function.pool {
                        //     pool.insert(ssa.clone());
                        // }
                        Ok(ssa)
                    }
                    Constant::Struct {
                        name,
                        values,
                        is_packed,
                    } => {
                        let name = name.as_ref().cloned().unwrap_or(format!("const_struct"));
                        let mut elements = vec![];
                        for (i, value) in values.iter().enumerate() {
                            let val = self.parse_operand(
                                None,
                                &Operand::ConstantOperand(value.to_owned()),
                                false,
                            )?;
                            match val.storage {
                                Storage::Constant { value, signed } => {
                                    elements.push(CompositeTypeStorage::Basic(value))
                                }
                                _ => todo!(),
                            }
                        }
                        let typ_storage = CompositeTypeStorage::Composite { elements };
                        let storage = Storage::StaticComposite {
                            typ_storage,
                            ident: name.to_owned(),
                            is_packed: *is_packed,
                        };
                        let ssa = Ssa::new(storage, InstructionSize::Unsized, name);
                        self.current_function.pool.insert(ssa.clone());
                        // let ssa = self.pool().push_composite(&name, typ_storage);

                        Ok(ssa)
                    }
                    Constant::BitCast(cast) => {
                        let operand = self.parse_operand(
                            None,
                            &Operand::ConstantOperand(cast.operand.to_owned()),
                            false,
                        )?;
                        dbg!(operand.storage);
                        todo!()
                    }
                    x => todo!("{}", x),
                }
            }
            Operand::LocalOperand { name, ty } => {
                if assert_exists {
                    // println!("{} MUST exist", name);
                    Ok(self.pool().get(&name.to_string()).unwrap())
                } else {
                    Ok(self.get_or_push_literal(
                        &name.to_string(),
                        Literal::default_for_size(op_size(ty)),
                    ))
                }
            }
            x => todo!("{}", x),
        }
    }

    fn get_or_push_literal(&mut self, name: &str, value: Literal) -> Ssa {
        if let Some(ssa) = self.pool().get(name) {
            ssa
        } else {
            self.pool().push_literal(name, value, false)
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
            globals.insert(data.name.clone(), data);
        }

        writeln!(self.output)?;

        self.current_function = Function::default();

        for func in self.module.clone().functions.iter() {
            self.current_function = Function::default();
            writeln!(self.current_function.prologue, "%{}", func.name)?;
            writeln!(self.current_function.prologue, "    push q bp")?;
            writeln!(self.current_function.prologue, "    mov q bp sp")?;

            self.current_function.name = func.name.to_owned();
            self.current_function.pool =
                RegPool::new(func.parameters.to_owned(), &mut self.current_function.body);
            for (_name, global) in globals.iter() {
                // println!("found global {}", global.name);
                self.pool().insert(global.clone());
            }
            self.current_function.last_block = Some(
                self.pool()
                    .get_unused("last_block", InstructionSize::Qword)
                    .unwrap(),
            );
            writeln!(
                self.current_function.body,
                "    mov q {} %{}",
                self.current_function
                    .last_block
                    .as_ref()
                    .unwrap()
                    .storage
                    .display(),
                func.name
            )?;
            println!("Function {}", self.current_function.name);
            for block in func.basic_blocks.iter() {
                let block_ssa = self.pool().label(&func.name, &block.name.to_string()[1..]);
                writeln!(
                    self.current_function.body,
                    "{}",
                    block_ssa.storage.display()
                )?;

                for instr in block.instrs.iter() {
                    // println!();
                    println!("  {}", instr);
                    // writeln!(self.current_function.body)?;
                    self.parse_instr(instr)?;
                }
                writeln!(
                    self.current_function.body,
                    "    mov q {} {}",
                    self.current_function
                        .last_block
                        .as_ref()
                        .unwrap()
                        .storage
                        .display(),
                    block_ssa.storage.display()
                )?;
                match &block.term {
                    Terminator::Ret(Ret { return_operand, .. }) => {
                        if let Some(ret) = return_operand.as_ref() {
                            let ret = self.parse_operand(None, ret, true)?;
                            writeln!(
                                self.current_function.epilogue,
                                "    mov{} ra {}",
                                ret.size,
                                ret.storage.display()
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
                            cond.size,
                            cond.storage.display()
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    jeq q {}",
                            false_dest.storage.display()
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    jmp q {}",
                            true_dest.storage.display()
                        )?;
                    }
                    Terminator::Br(Br { dest, .. }) => {
                        let dest = self.pool().label(&func.name, &dest.to_string());
                        writeln!(
                            self.current_function.body,
                            "    jmp q {}",
                            dest.storage.display()
                        )?;
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

mod tests {
    #[test]
    fn test_emit_k4sm() {
        use super::Parser;
        let mut parser = Parser::new("/home/cls/code/k4s/teststuff/test.bc");
        parser.emit_k4sm().unwrap();
        println!("{}", parser.output.clone());
    }
}
