use std::{fmt::Display, rc::Rc};

use k4s::{InstructionSize, Literal};
use llvm_ir::{
    types::{NamedStructDef, Types},
    Type, TypeRef,
};

use super::regpool::RegPool;

impl Ssa {
    pub fn parse_const(typref: &TypeRef, name: String, types: &Types, pool: &mut RegPool) -> Rc<Self> {
        match &**typref {
            Type::IntegerType { bits } => {
                let ssa = Self::Constant {
                    name,
                    value: Literal::from_bits_value(*bits, 0),
                    signed: false,
                };
                let ssa = Rc::new(ssa);
                pool.insert(ssa.clone());
                ssa
            }

            Type::StructType {
                element_types,
                is_packed,
            } => {
                let ssa = Self::StaticComposite {
                    ident: name.to_owned(),
                    elements: element_types
                        .iter()
                        .enumerate()
                        .map(|(i, elem)| {
                            Self::parse_const(elem, format!("{}_element{}", name, i), types, pool)
                        })
                        .collect(),
                    is_packed: *is_packed,
                };
                let ssa = Rc::new(ssa);
                pool.insert(ssa.clone());
                ssa
            },
            Type::NamedStructType { name } => {
                let def = types.named_struct_def(name).unwrap();
                match def {
                    NamedStructDef::Defined(struc) => {
                        Self::parse_const(struc, name.to_owned(), types, pool)
                    }
                    NamedStructDef::Opaque => todo!(),
                }
            }
            Type::ArrayType {
                element_type,
                num_elements,
            } => {
                assert!(
                    matches!(&**element_type, Type::IntegerType { bits: 8 }),
                    "{:?}",
                    &**element_type
                );
                let ssa = Self::Data {
                    label: name,
                    data: vec![0u8; *num_elements],
                };
                let ssa = Rc::new(ssa);
                pool.insert(ssa.clone());
                ssa
            }
            Type::PointerType { pointee_type, .. } => {
                if let Some(pointee) = pool.get(&format!("{}_pointee", name)) {
                    let ssa = Self::StaticPointer {
                        label: name,
                        pointee,
                    };
                    let ssa = Rc::new(ssa);
                    pool.insert(ssa.clone());
                    ssa
                } else {
                    let pointee =
                        Self::parse_const(pointee_type, format!("{}_pointee", name), types, pool);
                    let ssa = Self::StaticPointer {
                        label: name,
                        pointee,
                    };
                    let ssa = Rc::new(ssa);
                    pool.insert(ssa.clone());
                    ssa
                }
            }
            t => todo!("{:?}", t),
        }
    }

    pub fn push(typref: &TypeRef, name: String, types: &Types, pool: &mut RegPool) -> Rc<Self> {
        match &**typref {
            Type::IntegerType { bits } => {
                pool.push_literal(&name, Literal::from_bits_value(*bits, 0), false)
            }

            Type::StructType {
                element_types,
                is_packed,
            } => {
                let ssa = Self::Composite {
                    stack_offset: 0,
                    name: name.to_owned(),
                    elements: element_types
                        .iter()
                        .map(|elem| Self::push(elem, name.to_owned(), types, pool))
                        .collect(),
                    is_packed: *is_packed,
                };
                pool.push(ssa)
            }
            Type::NamedStructType { name } => {
                let def = types.named_struct_def(name).unwrap();
                match def {
                    NamedStructDef::Defined(struc) => {
                        Self::push(struc, name.to_owned(), types, pool)
                    }
                    NamedStructDef::Opaque => todo!(),
                }
            }
            Type::ArrayType {
                element_type,
                num_elements,
            } => {
                let mut elements = vec![];
                for i in 0..*num_elements {
                    elements.push(Self::push(element_type, format!("{}_elem{}", name, i), types, pool));
                }
                let ssa = Self::Array {
                    name,
                    stack_offset: 0,
                    elements,
                };
                pool.push(ssa)
            }
            Type::PointerType { pointee_type, .. } => {
                let pointee = Self::push(pointee_type, format!("{}_pointee", name), types, pool);
                pool.push_pointer(&name, pointee)
            }
            t => todo!("{:?}", t),
        }
    }

    pub fn size_in_bytes(&self) -> usize {
        match self {
            Self::Undef { size, .. } => size.in_bytes(),
            Self::NullPointer { .. } => InstructionSize::Qword.in_bytes(),
            Self::StaticPointer { .. } => InstructionSize::Qword.in_bytes(),
            Self::Register { size, .. } => size.in_bytes(),
            Self::Data { data, .. } => data.len(),
            Self::Constant { value, .. } => value.size().in_bytes(),
            Self::Label { .. } => InstructionSize::Qword.in_bytes(),
            Self::Pointer { .. } => InstructionSize::Qword.in_bytes(),
            Self::Composite { elements, .. } => {
                elements.iter().map(|elem| elem.size_in_bytes()).sum()
            }
            Self::StaticComposite { elements, .. } => {
                elements.iter().map(|elem| elem.size_in_bytes()).sum()
            }
            Self::Literal { value, .. } => value.size().in_bytes(),
            Self::Array { elements, .. } => {
                if elements.is_empty() {
                    0
                } else {
                    elements[0].size_in_bytes() * elements.len()
                }
            }
        }
    }

    pub fn size(&self) -> InstructionSize {
        match self.size_in_bytes() {
            1 => InstructionSize::Byte,
            2 => InstructionSize::Word,
            4 => InstructionSize::Dword,
            8 => InstructionSize::Qword,
            _ => InstructionSize::Unsized,
        }
    }

    pub fn byte_offset_of_element(&self, index: usize) -> u64 {
        match self {
            Self::Data { .. } => index as u64,
            Self::Composite { elements, .. } => {
                let mut total = 0;
                for elem in &elements[..index] {
                    total += elem.size_in_bytes();
                }
                total as u64
            }
            _ => todo!("{:?}", self),
        }
    }
}

#[derive(Hash, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Register {
    Rz,
    Ra,
    Rb,
    Rc,
    Rd,
    Re,
    Rf,
    Rg,
    Rh,
    Ri,
    Rj,
    Rk,
    Rl,
}

impl Register {
    pub fn display(&self) -> String {
        match self {
            Self::Rz => "rz",
            Self::Ra => "ra",
            Self::Rb => "rb",
            Self::Rc => "rc",
            Self::Rd => "rd",
            Self::Re => "re",
            Self::Rf => "rf",
            Self::Rg => "rg",
            Self::Rh => "rh",
            Self::Ri => "ri",
            Self::Rj => "rj",
            Self::Rk => "rk",
            Self::Rl => "rl",
        }
        .to_owned()
    }
}

#[derive(Hash, Clone, Debug)]
pub enum Ssa {
    // const/static storage
    Register {
        name: String,
        reg: Register,
        size: InstructionSize,
    },
    Data {
        label: String,
        data: Vec<u8>,
    },
    Label {
        label: String,
    },
    StaticPointer {
        label: String,
        pointee: Rc<Ssa>,
    },
    Constant {
        name: String,
        value: Literal,
        signed: bool,
    },
    StaticComposite {
        ident: String,
        is_packed: bool,
        elements: Vec<Rc<Ssa>>,
    },
    NullPointer {
        label: String,
    },
    Undef {
        name: String,
        size: InstructionSize,
    },
    // stack-allocated storage
    Literal {
        name: String,
        stack_offset: usize,
        value: Literal,
        signed: bool,
    },
    Pointer {
        name: String,
        stack_offset: usize,
        pointee: Rc<Ssa>,
    },
    Array {
        name: String,
        stack_offset: usize,
        elements: Vec<Rc<Ssa>>,
    },
    Composite {
        name: String,
        stack_offset: usize,
        is_packed: bool,
        elements: Vec<Rc<Ssa>>,
    },
}

impl Ssa {
    pub fn count(&self) -> usize {
        match self {
            Self::Data { label: _, data } => data.len(),
            _ => 1,
        }
    }

    pub fn stack_offset(&self) -> Option<usize> {
        match self {
            Self::Literal { stack_offset, .. } => Some(*stack_offset),
            Self::Pointer { stack_offset, .. } => Some(*stack_offset),
            Self::Composite { stack_offset, .. } => Some(*stack_offset),
            Self::Array { stack_offset, .. } => Some(*stack_offset),
            _ => None,
        }
    }

    pub fn name(&self) -> String {
        match self {
            Self::Undef { name, .. } => name.to_owned(),
            Self::StaticPointer { label, .. } => label.to_owned(),
            Self::Register { name, .. } => name.to_owned(),
            Self::StaticComposite { ident, .. } => ident.to_owned(),
            Self::Data { label, .. } => label.to_owned(),
            Self::Label { label, .. } => label.to_owned(),
            Self::Constant { name, .. } => name.to_owned(),
            Self::Literal { name, .. } => name.to_owned(),
            Self::Pointer { name, .. } => name.to_owned(),
            Self::Array { name, .. } => name.to_owned(),
            Self::Composite { name, .. } => name.to_owned(),
            Self::NullPointer { label: name } => name.to_owned(),
        }
    }

    pub fn duplicate(&self, new_name: &str) -> Rc<Self> {
        let mut this = self.clone();
        match &mut this {
            Ssa::Array { name, .. } => *name = new_name.to_owned(),
            Ssa::Register { name, .. } => *name = new_name.to_owned(),
            Ssa::Data { label, .. } => *label = new_name.to_owned(),
            Ssa::Label { label } => *label = new_name.to_owned(),
            Ssa::StaticPointer { label, .. } => *label = new_name.to_owned(),
            Ssa::Constant { name, .. } => *name = new_name.to_owned(),
            Ssa::StaticComposite { ident, .. } => *ident = new_name.to_owned(),
            Ssa::NullPointer { label } => *label = new_name.to_owned(),
            Ssa::Undef { name, .. } => *name = new_name.to_owned(),
            Ssa::Literal { name, .. } => *name = new_name.to_owned(),
            Ssa::Pointer { name, .. } => *name = new_name.to_owned(),
            Ssa::Composite { name, .. } => *name = new_name.to_owned(),
        }
        Rc::new(this)
    }

    pub fn display(&self) -> String {
        match self {
            Self::Undef { .. } => "BADBADBAD".to_owned(), // todo?
            Self::NullPointer { label } => label.to_owned(),
            Self::Register { reg, .. } => reg.display(),
            Self::StaticComposite { ident, .. } => ident.to_owned(),
            Self::Data { label, data: _ } => label.to_owned(),
            Self::Label { label } => label.to_owned(),
            Self::StaticPointer { label, .. } => label.to_owned(),
            Self::Constant { value, signed, .. } => {
                format!("${}", value.display_signed(*signed))
            }
            Self::Array { stack_offset, .. } => {
                format!("[-{stack_offset}+bp]")
            }
            Self::Composite { stack_offset, .. } => {
                format!("[-{stack_offset}+bp]")
            }
            Self::Literal { stack_offset, .. } => {
                format!("[-{stack_offset}+bp]")
            }
            Self::Pointer { stack_offset, .. } => {
                format!("[-{stack_offset}+bp]")
            }
        }
    }
}

impl Display for Ssa {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display())
    }
}
