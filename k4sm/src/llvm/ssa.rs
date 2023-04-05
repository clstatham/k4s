use k4s::{InstructionSize, Literal};
use llvm_ir::{
    types::{NamedStructDef, Types},
    Type, TypeRef,
};

#[derive(Clone, Hash, Debug)]
pub struct Ssa {
    pub name: String,
    pub storage: Storage,
    pub size: InstructionSize,
}

impl Ssa {
    pub fn new(storage: Storage, size: InstructionSize, name: String) -> Self {
        Self {
            name,
            storage,
            size,
        }
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum CompositeTypeStorage {
    Basic(Literal),
    Composite {
        elements: Vec<CompositeTypeStorage>,
    },
}

impl CompositeTypeStorage {
    pub fn parse(typref: &TypeRef, types: &Types) -> Self {
        match &**typref {
            Type::IntegerType { bits } => Self::Basic(Literal::from_bits_value(*bits, 0)),
            Type::StructType { element_types, is_packed } => Self::Composite {
                elements: element_types.iter().map(|elem| Self::parse(elem, types)).collect(),
            },
            Type::NamedStructType { name } => {
                let def = types.named_struct_def(name).unwrap();
                // let mut elements = vec![];
                match def {
                    NamedStructDef::Defined(struc) => Self::parse(struc, types),
                    NamedStructDef::Opaque => todo!()
                }
                // Self::Composite {
                //     elements,
                // }
            }
            _ => todo!(),
        }
    }

    pub fn size_in_bytes(&self) -> usize {
        match self {
            Self::Basic(lit) => lit.size().in_bytes(),
            Self::Composite { elements } => elements.iter().map(|elem| elem.size_in_bytes()).sum(),
        }
    }

    pub fn byte_offset_of_element(&self, index: usize) -> u64 {
        match self {
            Self::Basic(lit) => {
                assert_eq!(index, 0);
                0
            }
            Self::Composite { elements } => {
                let mut total = 0;
                for elem in &elements[..index] {
                    total += elem.size_in_bytes();
                }
                total as u64
            }
        }
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
// structs, mainly
pub struct CompositeType {
    pub ident: String,
    pub is_packed: bool,
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
        }.to_owned()
    }
}

#[derive(Hash, Clone, Debug)]
pub enum Storage {
    // static storage
    Register { 
        reg: Register,
    },
    Data {
        label: String,
        data: Vec<u8>,
    },
    Label {
        label: String,
    },
    Constant {
        value: Literal,
        signed: bool,
    },
    StaticComposite {
        ident: String,
        is_packed: bool,
        typ_storage: CompositeTypeStorage,
    },
    // stack-allocated storage
    Literal {
        stack_offset: usize,
        value: Literal,
        signed: bool,
    },
    Pointer {
        stack_offset: usize,
        pointee: Box<Ssa>,
    },
    Composite {
        stack_offset: usize,
        ident: String,
        is_packed: bool,
        typ_storage: CompositeTypeStorage,
    },
}

impl Storage {
    pub fn count(&self) -> usize {
        match self {
            Self::Data { label: _, data } => data.len(),
            _ => 1,
        }
    }

    pub fn stack_offset(&self) -> Option<usize> {
        match self {
            Self::Literal { stack_offset,.. } => Some(*stack_offset),
            Self::Pointer { stack_offset,.. } => Some(*stack_offset),
            Self::Composite { stack_offset,.. } => Some(*stack_offset),
            _ => None
        }
    }

    pub fn display(&self) -> String {
        match self {
            Self::Register { reg } => reg.display(),
            Self::StaticComposite { ident, .. } => ident.to_owned(),
            Self::Data { label, data: _ } => label.to_owned(),
            Self::Label { label } => label.to_owned(),
            Self::Constant { value, signed } => {
                format!("${}", value.display_signed(*signed))
            }
            Self::Composite { stack_offset, .. } => {
                format!("[-{stack_offset}+bp]")
            },
            Self::Literal { stack_offset, .. } => {
                format!("[-{stack_offset}+bp]")
            }
            Self::Pointer { stack_offset,  .. } => {
                format!("[-{stack_offset}+bp]")
            }
        }
    }
}
