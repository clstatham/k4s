use std::{fmt::Display, rc::Rc};

use k4s::{InstructionSize, Literal};
use llvm_ir::{
    types::{NamedStructDef, Types},
    Type,
};

use super::pool::Pool;


#[derive(Hash, Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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
    pub fn asm_repr(&self) -> String {
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

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.asm_repr())
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
        name: String,
        data: Vec<u8>,
    },
    Label {
        name: String,
    },
    StaticFunction {
        name: String,
        return_type: Type,
    },
    StaticPointer {
        name: String,
        pointee_type: Type,
        pointee: Option<Rc<Ssa>>,
    },
    Constant {
        name: String,
        value: Literal,
        signed: bool,
    },
    StaticComposite {
        name: String,
        is_packed: bool,
        element_types: Vec<Type>,
        elements: Vec<Rc<Ssa>>,
    },
    NullPointer {
        name: String,
    },
    Undef {
        name: String,
        size: InstructionSize,
    },

    // stack-allocated storage

    Primitive {
        name: String,
        stack_offset: usize,
        size: InstructionSize,
        signed: bool,
    },
    Pointer {
        name: String,
        stack_offset: usize,
        pointee_type: Type,
        // pointee: Option<Rc<Ssa>>,
    },
    Composite {
        name: String,
        stack_offset: usize,
        is_packed: bool,
        element_types: Vec<Type>,
        elements: Vec<Rc<Ssa>>,
    },
    Function {
        name: String,
        stack_offset: usize,
        return_type: Type,
    }
}

impl Ssa {
    pub fn stack_offset_mut(&mut self) -> Option<&mut usize> {
        match self {
            Self::Primitive { stack_offset, .. } => Some(stack_offset),
            Self::Pointer { stack_offset, .. } => Some(stack_offset),
            Self::Composite { stack_offset, .. } => Some(stack_offset),
            Self::Function { stack_offset, .. } => Some(stack_offset),
            _ => None
        }
    }

    pub fn parse_const(typref: &Type, name: String, types: &Types, pool: &mut Pool) -> Rc<Self> {
        match typref {
            Type::IntegerType { bits } => {
                let ssa = Self::Constant {
                    name,
                    value: Literal::from_bits_value_unsigned(*bits, 0),
                    signed: false,
                };
                let ssa = Rc::new(ssa);
                pool.insert(ssa.clone());
                ssa
            }
            Type::FPType(precision) => {
                match precision {
                    llvm_ir::types::FPType::Double => {
                        let ssa = Self::Constant {
                            name,
                            value: Literal::F64(0.into()),
                            signed: false,
                        };
                        let ssa = Rc::new(ssa);
                        pool.insert(ssa.clone());
                        ssa
                    }
                    llvm_ir::types::FPType::Single => {
                        let ssa = Self::Constant {
                            name,
                            value: Literal::F32(0.into()),
                            signed: false,
                        };
                        let ssa = Rc::new(ssa);
                        pool.insert(ssa.clone());
                        ssa
                    }
                    _ => todo!()
                }
            }

            Type::StructType {
                element_types,
                is_packed,
            } => {
                let ssa = Self::StaticComposite {
                    name: name.clone(),
                    elements: element_types
                        .iter()
                        .enumerate()
                        .map(|(i, elem)| {
                            Self::parse_const(elem, format!("{}_element{}", name, i), types, pool)
                        })
                        .collect(),
                    is_packed: *is_packed,
                    element_types: element_types.iter().map(|typ| typ.as_ref().to_owned()).collect(),
                };
                let ssa = Rc::new(ssa);
                pool.insert(ssa.clone());
                ssa
            }
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
                // assert!(
                //     matches!(&**element_type, Type::IntegerType { bits: 8 }),
                //     "{:?}",
                //     &**element_type
                // );
                if let Type::IntegerType { bits: 8 } = &**element_type {
                    let ssa = Self::Data {
                        name,
                        data: vec![0u8; *num_elements],
                    };
                    let ssa = Rc::new(ssa);
                    pool.insert(ssa.clone());
                    ssa
                } else {
                    let mut elements = vec![];
                    for i in 0..*num_elements {
                        elements.push(Self::parse_const(element_type, format!("{}_element{}", name, i), types, pool));
                    }
                    let ssa = Self::StaticComposite { name, is_packed: true, element_types: vec![element_type.as_ref().to_owned(); *num_elements], elements };
                    let ssa = Rc::new(ssa);
                    pool.insert(ssa.clone());
                    ssa
                }
                
            }
            Type::PointerType { pointee_type, .. } => {
                if let Some(pointee) = pool.get(&format!("{}_pointee", name)) {
                    let ssa = Self::StaticPointer { name, pointee: Some(pointee.clone()), pointee_type: pointee_type.as_ref().to_owned() };
                    let ssa = Rc::new(ssa);
                    pool.insert(ssa.clone());
                    ssa
                } else {
                    let pointee =
                        Self::parse_const(pointee_type, format!("{}_pointee", name), types, pool);
                    let ssa = Self::StaticPointer { name, pointee: Some(pointee), pointee_type: pointee_type.as_ref().to_owned() };
                    let ssa = Rc::new(ssa);
                    pool.insert(ssa.clone());
                    ssa
                }
            }
            Type::FuncType { result_type, .. } => {
                let ssa = Self::StaticFunction { name, return_type: result_type.as_ref().to_owned() };
                let ssa = Rc::new(ssa);
                pool.insert(ssa.clone());
                ssa
            }
            
            t => todo!("{:?}", t),
        }
    }

    pub fn push(typref: &Type, name: String, types: &Types, pool: &mut Pool) -> Rc<Self> {
        match typref {
            Type::IntegerType { bits } => {
                pool.push_primitive(&name, InstructionSize::from_n_bytes_unsigned(1.max(*bits / 8)), false)
            }
            Type::FPType(precision) => {
                match precision {
                    llvm_ir::types::FPType::Double => {
                        pool.push_primitive(&name, InstructionSize::F64, false)
                    }
                    llvm_ir::types::FPType::Single => {
                        pool.push_primitive(&name, InstructionSize::F32, false)
                    }
                    _ => todo!(),
                }
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
                        .enumerate()
                        .map(|(i, elem)| Self::push(elem, format!("{}_elem{}", name, i), types, pool))
                        .collect(),
                    is_packed: *is_packed,
                    element_types: element_types.iter().map(|typ| typ.as_ref().to_owned()).collect(),
                };
                pool.push(ssa)
            }
            Type::NamedStructType { name: struct_name } => {
                let def = types.named_struct_def(struct_name).unwrap();
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
                    elements.push(Self::push(
                        element_type,
                        format!("{}_elem{}", name, i),
                        types,
                        pool,
                    ));
                }
                let ssa = Self::Composite {
                    name,
                    stack_offset: 0,
                    elements,
                    is_packed: true,
                    element_types: vec![element_type.as_ref().to_owned(); *num_elements],
                };
                pool.push(ssa)
            }
            Type::PointerType { pointee_type, .. } => {
                pool.push_pointer(&name, pointee_type.as_ref().to_owned())
            }
            Type::FuncType { result_type, .. } => {
                let ssa = Self::Function { name, stack_offset: 0, return_type: result_type.as_ref().to_owned() };
                pool.push(ssa)
            }
            t => todo!("{:?}", t),
        }
    }

    pub fn size_in_bytes(&self) -> usize {
        match self {
            Self::StaticFunction { .. } => InstructionSize::U64.in_bytes(),
            Self::Function { .. } => InstructionSize::U64.in_bytes(),
            Self::Undef { size, .. } => size.in_bytes(),
            Self::NullPointer { .. } => InstructionSize::U64.in_bytes(),
            Self::StaticPointer { .. } => InstructionSize::U64.in_bytes(),
            Self::Register { size, .. } => size.in_bytes(),
            Self::Data { data, .. } => data.len(),
            Self::Constant { value, .. } => value.size().in_bytes(),
            Self::Label { .. } => InstructionSize::U64.in_bytes(),
            Self::Pointer { .. } => InstructionSize::U64.in_bytes(),
            Self::Composite { elements, .. } => {
                elements.iter().map(|elem| elem.size_in_bytes()).sum()
            }
            Self::StaticComposite { elements, .. } => {
                elements.iter().map(|elem| elem.size_in_bytes()).sum()
            }
            Self::Primitive { size, .. } => size.in_bytes(),
        }
    }

    pub fn size(&self) -> InstructionSize {
        match self.size_in_bytes() {
            1 => InstructionSize::U8,
            2 => InstructionSize::U16,
            4 => InstructionSize::U32,
            8 => InstructionSize::U64,
            _ => InstructionSize::U64,
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

    pub fn stack_offset(&self) -> Option<usize> {
        match self {
            Self::Primitive { stack_offset, .. } => Some(*stack_offset),
            Self::Pointer { stack_offset, .. } => Some(*stack_offset),
            Self::Composite { stack_offset, .. } => Some(*stack_offset),
            Self::Function { stack_offset, .. } => Some(*stack_offset),
            _ => None,
        }
    }

    pub fn name(&self) -> String {
        match self {
            Self::StaticFunction { name, .. } => name.to_owned(),
            Self::Function { name, .. } => name.to_owned(),
            Self::Undef { name, .. } => name.to_owned(),
            Self::StaticPointer { name, .. } => name.to_owned(),
            Self::Register { name, .. } => name.to_owned(),
            Self::StaticComposite { name, .. } => name.to_owned(),
            Self::Data { name, .. } => name.to_owned(),
            Self::Label { name, .. } => name.to_owned(),
            Self::Constant { name, .. } => name.to_owned(),
            Self::Primitive { name, .. } => name.to_owned(),
            Self::Pointer { name, .. } => name.to_owned(),
            Self::Composite { name, .. } => name.to_owned(),
            Self::NullPointer { name } => name.to_owned(),
        }
    }

    pub fn duplicate(&self, new_name: &str) -> Self {
        let mut this = self.clone();
        match &mut this {
            Ssa::StaticFunction { name, .. } => *name = new_name.to_owned(),
            Ssa::Function { name, .. } => *name = new_name.to_owned(),
            Ssa::Register { name, .. } => *name = new_name.to_owned(),
            Ssa::Data { name, .. } => *name = new_name.to_owned(),
            Ssa::Label { name } => *name = new_name.to_owned(),
            Ssa::StaticPointer { name, .. } => *name = new_name.to_owned(),
            Ssa::Constant { name, .. } => *name = new_name.to_owned(),
            Ssa::StaticComposite { name, .. } => *name = new_name.to_owned(),
            Ssa::NullPointer { name } => *name = new_name.to_owned(),
            Ssa::Undef { name, .. } => *name = new_name.to_owned(),
            Ssa::Primitive { name, .. } => *name = new_name.to_owned(),
            Ssa::Pointer { name, .. } => *name = new_name.to_owned(),
            Ssa::Composite { name, .. } => *name = new_name.to_owned(),
        }
        this
    }

    pub fn asm_repr(&self) -> String {
        match self {
            Self::Undef { .. } => "UNDEFINED".to_owned(), // todo?
            Self::NullPointer { name } => name.to_owned(),
            Self::Register { reg, .. } => reg.asm_repr(),
            Self::StaticComposite { name, .. } => name.to_owned(),
            Self::Data { name, data: _ } => name.to_owned(),
            Self::Label { name } => name.to_owned(),
            Self::StaticFunction { name, .. } => name.to_owned(),
            Self::StaticPointer { name, .. } => name.to_owned(),
            Self::Constant { value, .. } => {
                format!("$0x{:x}", value)
            }

            Self::Function { stack_offset, .. } => {
                format!("[-{stack_offset}+bp]")
            }
            Self::Composite { stack_offset, .. } => {
                format!("[-{stack_offset}+bp]")
            }
            Self::Primitive { stack_offset, .. } => {
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
        write!(f, "{}", self.asm_repr())
    }
}
