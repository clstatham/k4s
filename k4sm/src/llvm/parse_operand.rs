use std::{error::Error, fmt::Write, rc::Rc};

use k4s::{InstructionSize, Literal};
use llvm_ir::{types::Typed, Constant, Name, Operand, Type};

use super::{
    ssa::{Register, Ssa},
    Parser,
};

impl Parser {
    pub fn parse_operand(
        &mut self,
        name: Option<Name>,
        op: &Operand,
        assert_exists: bool,
    ) -> Result<Rc<Ssa>, Box<dyn Error>> {
        if let Some(ref name) = name {
            if let Some(ssa) = self.pool().get(&name.to_string()) {
                return Ok(ssa.clone());
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
                                size: InstructionSize::from_n_bytes_unsigned(1.max(*bits / 8)),
                            }))
                        } else {
                            let (value, signed) =
                                (Literal::from_bits_value_unsigned(*bits, *value), true);
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
                            return Ok(ssa.clone());
                        }
                        let ssa = Ssa::parse_const(
                            ty,
                            name.to_string(),
                            &self.module.types.to_owned(),
                            self.pool(),
                        );
                        let ptr = Rc::new(Ssa::StaticPointer {
                            name: name.to_string(),
                            pointee: Some(ssa),
                            pointee_type: ty.as_ref().to_owned(),
                        });
                        self.pool().insert(ptr.clone());

                        Ok(ptr)
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
                        let ptr = self.get_element_ptr(
                            &format!("{}_dest{}", src.name(), self.alloc_id()),
                            src,
                            indices,
                        )?;
                        Ok(ptr)
                    }
                    Constant::Array {
                        element_type,
                        elements,
                    } => {
                        // assert_eq!(**element_type, Type::IntegerType { bits: 8 });
                        if let Type::IntegerType { bits: 8 } = &**element_type {
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
                                    .unwrap_or(format!("%anon_data_{}", self.alloc_id()).into())
                                    .to_string()[1..]
                            );
                            let ssa = Rc::new(Ssa::Data {
                                name: data_label.clone(),
                                data: data.clone(),
                            });
                            writeln!(
                                self.output,
                                "{} align1 \"{}\"",
                                data_label,
                                // String::from_utf8(data).unwrap()
                                data.iter()
                                    .map(|byte| format!("\\x{:02x}", byte))
                                    .collect::<Vec<_>>()
                                    .join("")
                            )?;
                            self.current_function.pool.insert(ssa.clone());
                            Ok(ssa)
                        } else {
                            let name = name
                                .as_ref()
                                .cloned()
                                .map(|name| name.to_string())
                                // .or(name.map(|name| name.to_string()))
                                .unwrap_or(format!("const_array_{}", self.alloc_id()));
                            let mut values = vec![];
                            writeln!(self.output, "{}", name)?;
                            for (i, value) in elements.iter().enumerate() {
                                let val = self.parse_operand(
                                    Some(format!("{}_elem{}", &name[1..], i).into()),
                                    &Operand::ConstantOperand(value.to_owned()),
                                    false,
                                )?;
                                values.push(val);
                            }
                            let arr = Rc::new(Ssa::StaticComposite {
                                name: format!("{}_struc", &name),
                                is_packed: true,
                                elements: values,
                                element_types: vec![
                                    element_type.as_ref().to_owned();
                                    elements.len().max(1)
                                ],
                            });
                            let arr_ptr = Rc::new(Ssa::StaticPointer {
                                name: name.clone(),
                                pointee: Some(arr),
                                pointee_type: Type::ArrayType {
                                    element_type: element_type.to_owned(),
                                    num_elements: elements.len(),
                                },
                            });
                            self.pool().insert(arr_ptr.clone());

                            Ok(arr_ptr)
                        }
                    }
                    Constant::Struct {
                        name: struc_name,
                        values,
                        is_packed,
                    } => {
                        let name = struc_name
                            .as_ref()
                            .cloned()
                            .or(name.map(|name| name.to_string()))
                            .unwrap_or(format!("%const_struct_{}", self.alloc_id()));
                        let mut elements = vec![];
                        writeln!(self.output, "{}", name)?;
                        for (i, value) in values.iter().enumerate() {
                            let val = self.parse_operand(
                                Some(format!("@{}_elem{}", &name[1..], i).into()),
                                &Operand::ConstantOperand(value.to_owned()),
                                false,
                            )?;
                            elements.push(val);
                        }
                        let types = self.module.types.to_owned();
                        let struc = Rc::new(Ssa::StaticComposite {
                            name: format!("{}_struc", &name),
                            is_packed: *is_packed,
                            elements,
                            element_types: values
                                .iter()
                                .map(|val| val.get_type(&types).as_ref().to_owned())
                                .collect(),
                        });
                        let struc_ptr = Rc::new(Ssa::StaticPointer {
                            name: name.clone(),
                            pointee: Some(struc),
                            pointee_type: Type::StructType {
                                element_types: values
                                    .iter()
                                    .map(|val| val.get_type(&types))
                                    .collect(),
                                is_packed: *is_packed,
                            },
                        });
                        self.pool().insert(struc_ptr.clone());

                        Ok(struc_ptr)
                    }
                    Constant::BitCast(cast) => {
                        let operand = self.parse_operand(
                            None,
                            &Operand::ConstantOperand(cast.operand.to_owned()),
                            true,
                        )?;
                        self.pool().take(&operand.name()).unwrap();
                        // identity theft!
                        let ssa = Ssa::parse_const(
                            &cast.to_type,
                            operand.name(),
                            &self.module.types.to_owned(),
                            self.pool(),
                        );
                        Ok(ssa)
                    }
                    Constant::AggregateZero(typ) => {
                        let data_label = format!(
                            "%{}",
                            &name
                                .unwrap_or(format!("anon_data_{}", self.alloc_id()).into())
                                .to_string()[1..]
                        );
                        // let label = self.pool().label("", &data_label);

                        let ssa = Ssa::parse_const(
                            typ,
                            format!("{}_init", data_label),
                            &self.module.types.to_owned(),
                            self.pool(),
                        );
                        let label = Ssa::StaticPointer {
                            name: data_label,
                            pointee: Some(ssa.clone()),
                            pointee_type: typ.as_ref().to_owned(),
                        };
                        let label = Rc::new(label);
                        let size_bytes = ssa.size_in_bytes();
                        let align = ssa.size().in_bytes();
                        self.pool().insert(label.clone());
                        writeln!(self.output, "{}", label)?;
                        writeln!(
                            self.output,
                            "@{} align{} resb {}",
                            ssa.name(),
                            align,
                            size_bytes
                        )?;
                        Ok(label)
                    }
                    Constant::Null(_) => {
                        let data_label = format!(
                            "@{}",
                            &name
                                .unwrap_or(format!("null_data_{}", self.alloc_id()).into())
                                .to_string()[1..]
                        );
                        let ssa = Rc::new(Ssa::NullPointer { name: data_label });
                        self.pool().insert(ssa.clone());
                        let align = ssa.size().in_bytes();
                        writeln!(self.output, "{} align{} $0", ssa, align)?;
                        Ok(ssa)
                    }
                    Constant::Undef(und) => {
                        let data_label = format!(
                            "@{}",
                            &name
                                .unwrap_or(format!("undef_{}", self.alloc_id()).into())
                                .to_string()[1..]
                        );
                        let ssa = Ssa::parse_const(
                            und,
                            data_label,
                            &self.module.types.to_owned(),
                            self.pool(),
                        );
                        match ssa.as_ref() {
                            Ssa::StaticComposite { elements, .. } => {
                                for elem in elements.iter() {
                                    writeln!(
                                        self.output,
                                        "{} align{} resb {}",
                                        elem.name(),
                                        elem.size().in_bytes(),
                                        elem.size_in_bytes()
                                    )?;
                                }
                            }
                            _ => {
                                writeln!(
                                    self.output,
                                    "{} align{} resb {}",
                                    ssa.name(),
                                    ssa.size().in_bytes(),
                                    ssa.size_in_bytes()
                                )?;
                            }
                        }

                        Ok(ssa)
                    }
                    Constant::Float(f) => {
                        let data_label = format!(
                            "@{}",
                            &name
                                .unwrap_or(format!("float_{}", self.alloc_id()).into())
                                .to_string()[1..]
                        );
                        let (ssa, value) = match f {
                            llvm_ir::constant::Float::Double(f) => (
                                Ssa::Constant {
                                    name: data_label,
                                    value: Literal::F64(f.to_le_bytes().into()),
                                    signed: true,
                                },
                                *f,
                            ),
                            llvm_ir::constant::Float::Single(f) => (
                                Ssa::Constant {
                                    name: data_label,
                                    value: Literal::F32(f.to_le_bytes().into()),
                                    signed: true,
                                },
                                *f as f64,
                            ),
                            _ => todo!(),
                        };
                        let ssa = Rc::new(ssa);
                        self.pool().insert(ssa.clone());
                        let data = value.to_le_bytes();
                        let data = format!(
                            "\"{}\"",
                            data.iter()
                                .map(|byte| format!("\\x{:02x}", byte))
                                .collect::<Vec<_>>()
                                .join("")
                        );
                        writeln!(
                            self.output,
                            "{} align{} {}",
                            ssa.name(),
                            ssa.size().in_bytes(),
                            data
                        )?;
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
                        .unwrap_or_else(|| panic!("{:?} {:?}", name.to_string(), ty))
                        .clone())
                } else {
                    let types = &self.module.types.to_owned();
                    Ok(self.get_or_else(&name.to_string(), |pool| {
                        Ssa::push(ty, name.to_string(), types, pool)
                    }))
                }
            }
            x => todo!("{}", x),
        }
    }
}
