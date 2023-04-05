use std::{
    error::Error,
    fmt::Write,
    rc::Rc,
    sync::atomic::{Ordering},
};

use k4s::{InstructionSize, Literal};
use llvm_ir::{
    Constant, Name, Operand, Type,
};

use super::{Parser, ssa::{Ssa, Register}, op_size};


impl Parser {

    pub fn parse_operand(
        &mut self,
        name: Option<Name>,
        op: &Operand,
        assert_exists: bool,
    ) -> Result<Rc<Ssa>, Box<dyn Error>> {
        if let Some(ref name) = name {
            if let Some(ssa) = self.pool().get(&name.to_string()) {
                return Ok(ssa);
            }
        }
        match op {
            Operand::ConstantOperand(con) => {
                let con = &**con;
                match con {
                    Constant::Int { bits, value } => {
                        if *value == 0 {
                            Ok(Rc::new(Ssa::Register {
                                name: "rz".to_owned(),
                                reg: Register::Rz,
                                size: InstructionSize::from_n_bytes(1.max(*bits / 8)),
                            }))
                        } else {
                            let (value, signed) = (Literal::from_bits_value(*bits, *value), true);
                            Ok(Rc::new(Ssa::Constant {
                                name: name
                                    .as_ref()
                                    .map(|name| name.to_string())
                                    .unwrap_or(format!("{}", value.as_qword())),
                                value,
                                signed,
                            }))
                        }
                    }
                    Constant::GlobalReference { name, ty } => {
                        if let Some(ssa) = self.pool().get(&name.to_string()) {
                            return Ok(ssa);
                        }
                        match &**ty {
                            Type::ArrayType { .. } => {
                                let name = format!("@{}", &name.to_string()[1..]);
                                return Ok(self.pool().get(&name).unwrap());
                            }
                            Type::LabelType => return Ok(self.pool().label("", &name.to_string())),
                            Type::FuncType { .. } => {
                                return Ok(self.pool().label("", &name.to_string()))
                            }
                            Type::StructType { .. } => {
                                let ssa = Ssa::parse_const(
                                    ty,
                                    name.to_string(),
                                    &self.module.types.clone(),
                                    self.pool(),
                                );

                                Ok(ssa)
                            }
                            Type::NamedStructType { name } => {
                                let struc = self.module.types.named_struct(name);
                                let ssa = Ssa::parse_const(
                                    &struc,
                                    name.to_string(),
                                    &self.module.types.clone(),
                                    self.pool(),
                                );
                                dbg!(ssa);
                                todo!()
                            }
                            ty => {
                                todo!("{:?}", ty)
                            }
                        }
                    }
                    Constant::GetElementPtr(instr) => {
                        let indices = instr
                            .indices
                            .iter()
                            .map(|ind| {
                                self.parse_operand(
                                    None,
                                    &Operand::ConstantOperand(ind.to_owned()),
                                    false,
                                )
                                .unwrap()
                            })
                            .collect();

                        let src = self.parse_operand(
                            None,
                            &Operand::ConstantOperand(instr.address.clone()),
                            true,
                        )?;
                        let offset = self.get_element_ptr_const(src, indices)?;
                        self.pool().insert(offset.clone());
                        Ok(offset)
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
                        let data_label = format!(
                            "@{}",
                            &name
                                .unwrap_or(
                                    format!(
                                        "anon_data_{}",
                                        self.anon_datas.fetch_add(1, Ordering::SeqCst)
                                    )
                                    .into()
                                )
                                .to_string()[1..]
                        );
                        let ssa = Rc::new(Ssa::Data {
                            name: data_label.clone(),
                            data: data.clone(),
                        });
                        writeln!(
                            self.output,
                            "{} \"{}\"",
                            data_label,
                            data.iter()
                                .map(|byte| format!("\\x{:x}", byte))
                                .collect::<Vec<_>>()
                                .join("")
                        )?;
                        self.current_function.pool.insert(ssa.clone());
                        Ok(ssa)
                    }
                    Constant::Struct {
                        name: struc_name,
                        values,
                        ..
                    } => {
                        let name = struc_name
                            .as_ref()
                            .cloned()
                            .or(name.map(|name| name.to_string()))
                            .unwrap_or(format!(
                                "const_struct_{}",
                                self.anon_datas.fetch_add(1, Ordering::SeqCst)
                            ));
                        let mut elements = vec![];
                        writeln!(self.output, "{}", name)?;
                        let name = name.strip_prefix('%').unwrap_or(&name).to_owned();
                        let top_label = self.pool().label("", &name);
                        for (i, value) in values.iter().enumerate() {
                            let val = self.parse_operand(
                                Some(format!("{}_elem{}", name, i).into()),
                                &Operand::ConstantOperand(value.to_owned()),
                                false,
                            )?;
                            elements.push(val);
                        }

                        Ok(top_label)
                    }
                    Constant::BitCast(cast) => {
                        let operand = self.parse_operand(
                            None,
                            &Operand::ConstantOperand(cast.operand.to_owned()),
                            false,
                        )?;
                        match (operand.as_ref(), &*cast.to_type) {
                            // these are all basically TODO but i want to see if it breaks anything first
                            (Ssa::Label { .. }, Type::PointerType { .. }) => Ok(operand),
                            (Ssa::Data { .. }, Type::PointerType { .. }) => Ok(operand),
                            (Ssa::StaticComposite { .. }, Type::PointerType { .. }) => Ok(operand),
                            t => todo!("{:#?}", t),
                        }
                    }
                    Constant::AggregateZero(typ) => {
                        let data_label = format!(
                            "{}",
                            &name
                                .unwrap_or(
                                    format!(
                                        "anon_data_{}",
                                        self.anon_datas.fetch_add(1, Ordering::SeqCst)
                                    )
                                    .into()
                                )
                                .to_string()[1..]
                        );
                        let label = self.pool().label("", &data_label);
                        let ssa = Ssa::parse_const(
                            typ,
                            data_label.clone(),
                            &self.module.types.to_owned(),
                            self.pool(),
                        );
                        let size_bytes = ssa.size_in_bytes();
                        writeln!(self.output, "{}", label)?;
                        writeln!(self.output, "@{}_init resb {}", data_label, size_bytes,)?;
                        self.current_function.pool.insert(ssa.clone());
                        Ok(ssa)
                    }
                    Constant::Null(_) => {
                        let data_label = format!(
                            "@{}",
                            &name
                                .unwrap_or(
                                    format!(
                                        "null_data_{}",
                                        self.anon_datas.fetch_add(1, Ordering::SeqCst)
                                    )
                                    .into()
                                )
                                .to_string()[1..]
                        );
                        let ssa = Rc::new(Ssa::NullPointer { name: data_label });
                        self.pool().insert(ssa.clone());
                        writeln!(self.output, "{} $0", ssa)?;
                        Ok(ssa)
                    }
                    Constant::Undef(und) => {
                        let ssa = Rc::new(Ssa::Undef {
                            name: format!(
                                "undef_{}_{}",
                                op_size(und),
                                self.anon_datas.fetch_add(1, Ordering::SeqCst)
                            ),
                            size: op_size(und),
                        });
                        self.pool().insert(ssa.clone());
                        Ok(ssa)
                    }
                    x => todo!("{}", x),
                }
            }
            Operand::LocalOperand { name, ty } => {
                if assert_exists {
                    Ok(self
                        .pool()
                        .get(&name.to_string())
                        .unwrap_or_else(|| panic!("{:?} {:?}", name.to_string(), ty)))
                } else {
                    Ok(self.get_or_push_primitive(
                        &name.to_string(),
                        Literal::default_for_size(op_size(ty)),
                    ))
                }
            }
            x => todo!("{}", x),
        }
    }
}