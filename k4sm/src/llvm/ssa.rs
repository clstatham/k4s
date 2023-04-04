use k4s::{OpSize, Literal};


#[derive(Clone)]
pub struct Ssa {
    pub name: String,
    pub storage: Storage,
    pub size: OpSize,
}

impl Ssa {
    pub fn new(storage: Storage, size: OpSize, name: String) -> Self {
        Self {
            name,
            storage,
            size,
        }
    }
}

const ALL_REGS: &[Storage] = &[
    Storage::Ra,
    Storage::Rb,
    Storage::Rc,
    Storage::Rd,
    Storage::Re,
    Storage::Rf,
    Storage::Rg,
    Storage::Rh,
    Storage::Ri,
    Storage::Rj,
    Storage::Rk,
    Storage::Rl,
];

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum Storage {
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
    Constant { value: Literal, signed: bool },
    Label { name: String },
    BpOffset { off: isize, pointed_size: OpSize },
    Data { label: String, data: Vec<u8> },
}

impl Storage {
    pub fn display(&self) -> String {
        let s = match self {
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
            Self::Data { label, data: _ } => return label.to_owned(),
            Self::Label { name } => return name.to_owned(),
            Self::Constant { value, signed } => {
                return format!("${}", value.display_signed(*signed))
            }
            Self::BpOffset { off, pointed_size: _ } => {
                return format!("[{off}+bp]");
            }
        };
        s.to_owned()
    }
}
