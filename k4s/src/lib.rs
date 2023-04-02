use std::collections::{BTreeMap, HashMap, HashSet};

use zerocopy::{LittleEndian, U16, U32, U64};

pub const HEADER_MAGIC: &[u8] = b"k4d\x13\x37";
pub const HEADER_ENTRY_POINT: &[u8] = b"ent";
pub const HEADER_END: &[u8] = b"\x69\x69d4k";

pub const LIT: u8 = 0xff;
pub const OFFSET: u8 = 0xfe;

bitflags::bitflags! {
    #[derive(PartialEq, Eq, Clone, Copy)]
    pub struct ValidOpArgs: u16 {
        const NOARGS =   0b1;
        const VAL =      0b10;
        const ADR =      0b100;
        const VAL_VAL =  0b1000;
        const VAL_ADR =  0b10000;
        const ADR_VAL =  0b100000;
        const ADR_ADR =  0b1000000;
    }
}

impl ValidOpArgs {
    pub fn into_op_args_vec(self) -> Vec<OpArgs> {
        let mut out = vec![];
        if self.contains(Self::NOARGS) {
            out.push(OpArgs::NoArgs);
        }
        if self.contains(Self::VAL) {
            out.push(OpArgs::Val);
        }
        if self.contains(Self::ADR) {
            out.push(OpArgs::Adr);
        }
        if self.contains(Self::VAL_VAL) {
            out.push(OpArgs::ValVal);
        }
        if self.contains(Self::VAL_ADR) {
            out.push(OpArgs::ValAdr);
        }
        if self.contains(Self::ADR_VAL) {
            out.push(OpArgs::AdrVal);
        }
        if self.contains(Self::ADR_ADR) {
            out.push(OpArgs::AdrAdr);
        }
        out
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub enum OpArgs {
    NoArgs,
    Val,
    Adr,
    ValVal,
    ValAdr,
    AdrVal,
    AdrAdr,
}

impl OpArgs {
    pub fn basic_str_rep(&self) -> &'static str {
        match *self {
            Self::NoArgs => "",
            Self::Val => "a",
            Self::Adr => "[a]",
            Self::ValVal => "a a",
            Self::ValAdr => "a [a]",
            Self::AdrVal => "[a] a",
            Self::AdrAdr => "[a] [a]",
        }
    }
    pub fn extended_str_reps(&self) -> Vec<&'static str> {
        let mut out = vec![];
        if matches!(self, Self::Val) {
            out.push("a");
            out.push("[0+a]")
        } else if matches!(self, Self::Adr) {
            out.push("[a]");
            out.push("[[0+a]]");
        } else if matches!(self, Self::ValVal) {
            out.push("a a");
            out.push("[0+a] a");
            out.push("a [0+a]");
            out.push("[0+a] [0+a]");
        } else if matches!(self, Self::ValAdr) {
            out.push("a [a]");
            out.push("a [[0+a]]");
            out.push("[0+a] [a]");
            out.push("[0+a] [[0+a]]");
        } else if matches!(self, Self::AdrVal) {
            out.push("[a] a");
            out.push("[[0+a]] a");
            out.push("[a] [0+a]");
            out.push("[[0+a]] [0+a]");
        } else if matches!(self, Self::AdrAdr) {
            out.push("[a] [a]");
            out.push("[[0+a]] [a]");
            out.push("[a] [[0+a]]");
            out.push("[[0+a]] [[0+a]]");
        }
        out
    }
}

#[derive(PartialEq, Eq, Hash)]
pub struct Op {
    mnemonic: &'static str,
    op_args: Vec<OpArgs>,
}

impl Op {
    pub fn basic_str_reps(&self) -> Vec<String> {
        self.op_args.iter().map(|arg| format!("{} {}", self.mnemonic, arg.basic_str_rep())).collect()
    }
}

#[derive(PartialEq, Eq, Hash)]
pub struct OpVariant {
    pub mnemonic: String,
    pub op_args: OpArgs,
}

impl OpVariant {
    pub fn basic_str_rep(&self) -> String {
        format!("{} {}", self.mnemonic, self.op_args.basic_str_rep())
    }

    pub fn extended_str_reps(&self) -> Vec<String> {
        self.op_args.extended_str_reps().iter().map(|rep| format!("{} {}", self.mnemonic, rep)).collect()
    }
}

#[rustfmt::skip]
pub fn valid_ops() -> Vec<Op> {
    vec![
        Op { mnemonic: "nop", op_args: (ValidOpArgs::NOARGS).into_op_args_vec() },
        Op { mnemonic: "hlt", op_args: (ValidOpArgs::NOARGS).into_op_args_vec() },
        Op { mnemonic: "ret", op_args: (ValidOpArgs::NOARGS).into_op_args_vec() },
        Op { mnemonic: "mov", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec() },
        Op { mnemonic: "push", op_args: (ValidOpArgs::VAL | ValidOpArgs::ADR).into_op_args_vec() },
        Op { mnemonic: "pop", op_args: (ValidOpArgs::VAL | ValidOpArgs::ADR).into_op_args_vec() },
        Op { mnemonic: "printi", op_args: (ValidOpArgs::VAL | ValidOpArgs::ADR).into_op_args_vec() },
        Op { mnemonic: "printc", op_args: (ValidOpArgs::VAL | ValidOpArgs::ADR).into_op_args_vec() },
        Op { mnemonic: "add", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec() },
        Op { mnemonic: "sub", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec() },
        Op { mnemonic: "mul", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec() },
        Op { mnemonic: "div", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec() },
        Op { mnemonic: "mod", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec() },
        Op { mnemonic: "and", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec() },
        Op { mnemonic: "or", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec() },
        Op { mnemonic: "xor", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec() },
        Op { mnemonic: "cmp", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec() },
        Op { mnemonic: "jmp", op_args: (ValidOpArgs::VAL).into_op_args_vec() },
        Op { mnemonic: "jgt", op_args: (ValidOpArgs::VAL).into_op_args_vec() },
        Op { mnemonic: "jlt", op_args: (ValidOpArgs::VAL).into_op_args_vec() },
        Op { mnemonic: "jeq", op_args: (ValidOpArgs::VAL).into_op_args_vec() },
        Op { mnemonic: "jne", op_args: (ValidOpArgs::VAL).into_op_args_vec() },
        Op { mnemonic: "call", op_args: (ValidOpArgs::VAL).into_op_args_vec() },
        Op { mnemonic: "shl", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec() },
        Op { mnemonic: "shr", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec() },
    ]
}

pub fn gen_bytecodes() -> HashMap<OpVariant, u8> {
    let mut out = HashMap::new();
    let mut i: u8 = 0;
    for op in valid_ops() {
        for variant in op.op_args {
            out.insert(OpVariant { mnemonic: op.mnemonic.to_owned(), op_args: variant }, i);
            i = i.checked_add(1).expect("Too many op variants!");
        }
    }
    out
}

pub fn gen_regs() -> HashMap<&'static str, u8> {
    [
        "ra", "rb", "rc", "rd", "re", "rf", "rg", "rh", "ri", "rj", "rk", "rl", "bp", "sp", "pc",
        "fl",
    ]
    .into_iter()
    .enumerate()
    .map(|(i, reg)| (reg, i.try_into().unwrap()))
    .collect()
}

pub type Qword = U64<LittleEndian>;
pub type Dword = U32<LittleEndian>;
pub type Word = U16<LittleEndian>;
pub type Byte = u8;

bitflags::bitflags! {
    #[derive(Debug, Default, Clone, Copy)]
    #[repr(transparent)]
    pub struct Fl: u64 {
        const EQ = 0b1;
        const GT = 0b10;
    }
}

impl Fl {
    pub fn eq(self) -> bool {
        self.contains(Self::EQ)
    }
    pub fn gt(self) -> bool {
        self.contains(Self::GT)
    }
    pub fn lt(self) -> bool {
        !self.contains(Self::GT) && !self.contains(Self::EQ)
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub struct Regs {
    pub ra: Qword,
    pub rb: Qword,
    pub rc: Qword,
    pub rd: Qword,
    pub re: Qword,
    pub rf: Qword,
    pub rg: Qword,
    pub rh: Qword,
    pub ri: Qword,
    pub rj: Qword,
    pub rk: Qword,
    pub rl: Qword,

    pub bp: Qword,
    pub sp: Qword,
    pub pc: Qword,
    pub fl: Fl,
}

impl Regs {
    pub fn get_qword(&self, reg: Byte, regs_map: &HashMap<&Byte, &&str>) -> Qword {
        match *regs_map[&reg] {
            "ra" => self.ra,
            "rb" => self.rb,
            "rc" => self.rc,
            "rd" => self.rd,
            "re" => self.re,
            "rf" => self.rf,
            "rg" => self.rg,
            "rh" => self.rh,
            "ri" => self.ri,
            "rj" => self.rj,
            "rk" => self.rk,
            "rl" => self.rl,
            "bp" => self.bp,
            "sp" => self.sp,
            "pc" => self.pc,
            "fl" => Qword::new(self.fl.bits()),
            _ => unreachable!(),
        }
    }

    pub fn set_qword(&mut self, reg: Byte, val: Qword, regs_map: &HashMap<&Byte, &&str>) {
        match *regs_map[&reg] {
            "ra" => self.ra = val,
            "rb" => self.rb = val,
            "rc" => self.rc = val,
            "rd" => self.rd = val,
            "re" => self.re = val,
            "rf" => self.rf = val,
            "rg" => self.rg = val,
            "rh" => self.rh = val,
            "ri" => self.ri = val,
            "rj" => self.rj = val,
            "rk" => self.rk = val,
            "rl" => self.rl = val,
            "bp" => self.bp = val,
            "sp" => self.sp = val,
            "pc" => self.pc = val,
            "fl" => self.fl = Fl::from_bits_truncate(val.get()),
            _ => unreachable!(),
        }
    }
}
