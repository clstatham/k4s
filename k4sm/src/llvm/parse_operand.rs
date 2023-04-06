use std::{error::Error, fmt::Write, rc::Rc};

use k4s::{InstructionSize, Literal};
use llvm_ir::{Constant, Name, Operand, Type};

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
                            return Ok(ssa.clone());
                        }
                        return Ok(Ssa::parse_const(ty, name.to_string(), &self.module.types.to_owned(), self.pool()))
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
                        let ptr = self.get_element_ptr(&format!("{}_dest{}", src.name(), self.alloc_id()), src, indices)?;
                        Ok(ptr)
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
                                        "%anon_data_{}",
                                        self.alloc_id()
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
                            String::from_utf8(data).unwrap()
                            // data.iter()
                                // .map(|byte| format!("\\x{:02x}", byte))
                                // .collect::<Vec<_>>()
                                // .join("")
                        )?;
                        self.current_function.pool.insert(ssa.clone());
                        Ok(ssa)
                    }
                    Constant::Struct {
                        name: struc_name,
                        values,
                        is_packed
                    } => {
                        let name = struc_name
                            .as_ref()
                            .cloned()
                            .or(name.map(|name| name.to_string()))
                            .unwrap_or(format!(
                                "const_struct_{}",
                                self.alloc_id()
                            ));
                        let mut elements = vec![];
                        writeln!(self.output, "{}", name)?;
                        for (i, value) in values.iter().enumerate() {
                            let val = self.parse_operand(
                                Some(format!("{}_elem{}", &name[1..], i).into()),
                                &Operand::ConstantOperand(value.to_owned()),
                                false,
                            )?;
                            elements.push(val);
                        }
                        let struc = Rc::new(Ssa::StaticComposite { name: format!("{}_struc", &name), is_packed: *is_packed, elements });
                        let struc_ptr = Rc::new(Ssa::StaticPointer { name: name.clone(), pointee: Some(struc) });
                        self.pool().insert(struc_ptr.clone());

                        Ok(struc_ptr)
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
                                        self.alloc_id()
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
                        writeln!(self.output, "@{}_init resb {}", data_label, size_bytes)?;
                        Ok(ssa)
                    }
                    Constant::Null(_) => {
                        let data_label = format!(
                            "@{}",
                            &name
                                .unwrap_or(
                                    format!(
                                        "null_data_{}",
                                        self.alloc_id()
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
                        let data_label = format!(
                            "@{}",
                            &name
                                .unwrap_or(
                                    format!(
                                        "undef_{}",
                                        self.alloc_id()
                                    )
                                    .into()
                                )
                                .to_string()[1..]
                        );
                        let ssa = Ssa::parse_const(und, data_label, &self.module.types.to_owned(), self.pool());
                        match ssa.as_ref() {
                            Ssa::StaticComposite { elements, .. } => {
                                for elem in elements.iter() {
                                    writeln!(self.output, "{} resb {}", elem.name(), elem.size_in_bytes())?;
                                }
                            }
                            _ => {writeln!(self.output, "{} resb {}", ssa.name(), ssa.size_in_bytes())?;}
                        }
                        
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
                        .unwrap_or_else(|| panic!("{:?} {:?}", name.to_string(), ty)).clone())
                } else {
                    let types = &self.module.types.to_owned();
                    Ok(self.get_or_else(
                        &name.to_string(),
                        |pool| Ssa::push(ty, name.to_string(), types, pool),
                    ))
                }
            }
            x => todo!("{}", x),
        }
    }
}
