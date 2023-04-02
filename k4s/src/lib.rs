use std::{collections::{HashMap}, fmt::{Display, LowerHex}, ops::{Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, Shl, Shr}};

use zerocopy::{LittleEndian, U16, U32, U64};

pub const HEADER_MAGIC: &[u8] = b"k4d\x13\x37";
pub const HEADER_ENTRY_POINT: &[u8] = b"ent";
pub const HEADER_END: &[u8] = b"\x69\x69d4k";

pub const LIT: u8 = 0xff;
pub const OFFSET: u8 = 0xfe;


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operand {
    Byte(Byte),
    Word(Word),
    Dword(Dword),
    Qword(Qword),
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Byte(a) => write!(f, "{}", a),
            Self::Word(a) => write!(f, "{}", a),
            Self::Dword(a) => write!(f, "{}", a),
            Self::Qword(a) => write!(f, "{}", a),
        }
    }
}

impl LowerHex for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Byte(a) => write!(f, "{:x}", a),
            Self::Word(a) => write!(f, "{:x}", a),
            Self::Dword(a) => write!(f, "{:x}", a),
            Self::Qword(a) => write!(f, "{:x}", a),
        }
    }
}

impl Operand {
    pub fn new(size: OpSize, raw: Qword) -> Self {
        match size {
            OpSize::Byte => {
                let b: Byte = (raw.get() & Byte::MAX as u64) as Byte;
                Self::Byte(b)
            }
            OpSize::Word => {
                let max: Qword = Word::MAX_VALUE.into();
                let w: u16 =  (raw.get() & max.get()) as u16;
                Self::Word(w.into())
            }
            OpSize::Dword => {
                let max: Qword = Dword::MAX_VALUE.into();
                let w: u32 =  (raw.get() & max.get()) as u32;
                Self::Dword(w.into())
            }
            OpSize::Qword => {
                Self::Qword(raw)
            }
            OpSize::Unsized => unimplemented!(),
        }
    }

    pub fn size(self) -> OpSize {
        match self {
            Self::Byte(_) => OpSize::Byte,
            Self::Word(_) => OpSize::Word,
            Self::Dword(_) => OpSize::Dword,
            Self::Qword(_) => OpSize::Qword,
        }
    }

    pub fn as_byte(self) -> Byte {
        match self {
            Self::Byte(a) => a,
            Self::Word(a) => ((a.get() as u64) & Byte::MAX as u64) as Byte,
            Self::Dword(a) => ((a.get() as u64) & Byte::MAX as u64) as Byte,
            Self::Qword(a) => ((a.get()) & Byte::MAX as u64) as Byte,
        }
    }
    pub fn as_word(self) -> Word {
        match self {
            Self::Byte(a) => (a as u16).into(),
            Self::Word(a) => a,
            Self::Dword(a) => (((a.get() as u64) & Word::MAX_VALUE.get() as u64) as u16).into(),
            Self::Qword(a) => (((a.get()) & Word::MAX_VALUE.get() as u64) as u16).into(),
        }
    }
    pub fn as_dword(self) -> Dword {
        match self {
            Self::Byte(a) => (a as u32).into(),
            Self::Word(a) => (a.get() as u32).into(),
            Self::Dword(a) => a,
            Self::Qword(a) => (((a.get()) & Dword::MAX_VALUE.get() as u64) as u32).into(),
        }
    }
    pub fn as_qword(self) -> Qword {
        match self {
            Self::Byte(a) => (a as u64).into(),
            Self::Word(a) => (a.get() as u64).into(),
            Self::Dword(a) => (a.get() as u64).into(),
            Self::Qword(a) => a,
        }
    }
}

impl Add<Operand> for Operand {
    type Output = Self;
    fn add(self, rhs: Operand) -> Self::Output {
        Self::new(self.size(), (self.as_qword().get() + rhs.as_qword().get()).into())
    }
}

impl Sub<Operand> for Operand {
    type Output = Self;
    fn sub(self, rhs: Operand) -> Self::Output {
        Self::new(self.size(), (self.as_qword().get() - rhs.as_qword().get()).into())
    }
}

impl Mul<Operand> for Operand {
    type Output = Self;
    fn mul(self, rhs: Operand) -> Self::Output {
        Self::new(self.size(), (self.as_qword().get() * rhs.as_qword().get()).into())
    }
}

impl Div<Operand> for Operand {
    type Output = Self;
    fn div(self, rhs: Operand) -> Self::Output {
        Self::new(self.size(), (self.as_qword().get() / rhs.as_qword().get()).into())
    }
}

impl Rem<Operand> for Operand {
    type Output = Self;
    fn rem(self, rhs: Operand) -> Self::Output {
        Self::new(self.size(), (self.as_qword().get() % rhs.as_qword().get()).into())
    }
}

impl BitAnd<Operand> for Operand {
    type Output = Self;
    fn bitand(self, rhs: Operand) -> Self::Output {
        Self::new(self.size(), (self.as_qword().get() & rhs.as_qword().get()).into())
    }
}

impl BitOr<Operand> for Operand {
    type Output = Self;
    fn bitor(self, rhs: Operand) -> Self::Output {
        Self::new(self.size(), (self.as_qword().get() | rhs.as_qword().get()).into())
    }
}

impl BitXor<Operand> for Operand {
    type Output = Self;
    fn bitxor(self, rhs: Operand) -> Self::Output {
        Self::new(self.size(), (self.as_qword().get() ^ rhs.as_qword().get()).into())
    }
}

impl Shl<Operand> for Operand {
    type Output = Self;
    fn shl(self, rhs: Operand) -> Self::Output {
        Self::new(self.size(), (self.as_qword().get() << rhs.as_qword().get()).into())
    }
}

impl Shr<Operand> for Operand {
    type Output = Self;
    fn shr(self, rhs: Operand) -> Self::Output {
        Self::new(self.size(), (self.as_qword().get() >> rhs.as_qword().get()).into())
    }
}



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
            // out.push("[[0+a]]");
        } else if matches!(self, Self::ValVal) {
            out.push("a a");
            out.push("[0+a] a");
            out.push("a [0+a]");
            out.push("[0+a] [0+a]");
        } else if matches!(self, Self::ValAdr) {
            out.push("a [a]");
            // out.push("a [[0+a]]");
            out.push("[0+a] [a]");
            // out.push("[0+a] [[0+a]]");
        } else if matches!(self, Self::AdrVal) {
            out.push("[a] a");
            // out.push("[[0+a]] a");
            out.push("[a] [0+a]");
            // out.push("[[0+a]] [0+a]");
        } else if matches!(self, Self::AdrAdr) {
            out.push("[a] [a]");
            // out.push("[[0+a]] [a]");
            // out.push("[a] [[0+a]]");
            // out.push("[[0+a]] [[0+a]]");
        }
        out
    }
}


#[derive(PartialEq, Eq, Hash)]
pub struct Op {
    mnemonic: &'static str,
    op_args: Vec<OpArgs>,
    valid_sizes: Vec<OpSize>,
}

impl Op {
    pub fn basic_str_reps(&self) -> Vec<String> {
        let mut out = Vec::new();
        self.op_args.iter().for_each(|arg| self.valid_sizes.iter().for_each(|size| {
            let size = match size {
                OpSize::Byte => " b",
                OpSize::Word => " w",
                OpSize::Dword => " d",
                OpSize::Qword => " q",
                OpSize::Unsized => "",
            };
            out.push(format!("{}{} {}", self.mnemonic, size, arg.basic_str_rep()))
        }));
        out
    }
}

#[derive(PartialEq, Eq, Hash)]
pub struct OpVariant {
    pub mnemonic: String,
    pub op_args: OpArgs,
    pub n_args: usize,
    pub metadata: MetadataByte,
}

impl OpVariant {
    pub fn basic_str_rep(&self) -> String {
        // let size = match self.metadata.0 & 0b111 {
        //     0b000 => " b",
        //     0b001 => " w",
        //     0b010 => " d",
        //     0b011 => " q",
        //     0b100 => "",
        //     _ => unreachable!(),
        // };
        format!("{} {}", self.mnemonic, self.op_args.basic_str_rep())
    }

    pub fn extended_str_reps(&self) -> Vec<String> {
        let size = match self.metadata.0 & 0b111 {
            0b000 => " b",
            0b001 => " w",
            0b010 => " d",
            0b011 => " q",
            0b100 => "",
            _ => unreachable!(),
        };
        self.op_args.extended_str_reps().iter().map(|rep| format!("{}{} {}", self.mnemonic, size, rep)).collect()
    }
}

#[rustfmt::skip]
pub fn valid_ops() -> Vec<Op> {
    vec![
        Op { mnemonic: "nop", op_args: (ValidOpArgs::NOARGS).into_op_args_vec(), valid_sizes: vec![OpSize::Unsized] },
        Op { mnemonic: "hlt", op_args: (ValidOpArgs::NOARGS).into_op_args_vec(), valid_sizes: vec![OpSize::Unsized] },
        Op { mnemonic: "ret", op_args: (ValidOpArgs::NOARGS).into_op_args_vec(), valid_sizes: vec![OpSize::Unsized] },
        Op { mnemonic: "mov", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "push", op_args: (ValidOpArgs::VAL | ValidOpArgs::ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "pop", op_args: (ValidOpArgs::VAL | ValidOpArgs::ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "printi", op_args: (ValidOpArgs::VAL | ValidOpArgs::ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "printc", op_args: (ValidOpArgs::VAL | ValidOpArgs::ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "add", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "sub", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "mul", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "div", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "mod", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "and", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "or", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "xor", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "cmp", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "jmp", op_args: (ValidOpArgs::VAL).into_op_args_vec(), valid_sizes: vec![OpSize::Unsized] },
        Op { mnemonic: "jgt", op_args: (ValidOpArgs::VAL).into_op_args_vec(), valid_sizes: vec![OpSize::Unsized] },
        Op { mnemonic: "jlt", op_args: (ValidOpArgs::VAL).into_op_args_vec(), valid_sizes: vec![OpSize::Unsized] },
        Op { mnemonic: "jeq", op_args: (ValidOpArgs::VAL).into_op_args_vec(), valid_sizes: vec![OpSize::Unsized] },
        Op { mnemonic: "jne", op_args: (ValidOpArgs::VAL).into_op_args_vec(), valid_sizes: vec![OpSize::Unsized] },
        Op { mnemonic: "call", op_args: (ValidOpArgs::VAL).into_op_args_vec(), valid_sizes: vec![OpSize::Unsized] },
        Op { mnemonic: "shl", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
        Op { mnemonic: "shr", op_args: (ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR).into_op_args_vec(), valid_sizes: vec![OpSize::Byte, OpSize::Word, OpSize::Dword, OpSize::Qword] },
    ]
}

pub fn gen_bytecodes() -> HashMap<OpVariant, [u8; 2]> {
    let mut out = HashMap::new();
    let mut i: u8 = 0;
    for op in valid_ops() {
        for variant in op.op_args {
            let n_args = variant.basic_str_rep().split_whitespace().count();
            for operand_size in &op.valid_sizes {
                let metadata = MetadataByte::new(*operand_size);
                out.insert(OpVariant { mnemonic: op.mnemonic.to_owned(), op_args: variant, n_args, metadata }, [i, metadata.0]);
            }
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

bitflags::bitflags! {
    pub struct MetadataByteFlags: u8 {
        // todo
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum OpSize {
    Byte = 0,
    Word = 1,
    Dword = 2,
    Qword = 3,
    Unsized = 4,
}

impl Display for OpSize {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Byte => write!(f, " b"),
            Self::Word => write!(f, " w"),
            Self::Dword => write!(f, " d"),
            Self::Qword => write!(f, " q"),
            Self::Unsized => write!(f, ""),
        }
    }
}

impl OpSize {
    pub fn as_metadata(self) -> u8 {
        self as u8
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct MetadataByte(u8);

impl MetadataByte {
    pub fn new(operand_size: OpSize) -> Self {
        Self(operand_size.as_metadata()) // todo: more options
    }



    pub fn op_size(self) -> OpSize {
        match self.0 & 0b111 {
            0b000 => OpSize::Byte,
            0b001 => OpSize::Word,
            0b010 => OpSize::Dword,
            0b011 => OpSize::Qword,
            0b100 => OpSize::Unsized,
            _ => unreachable!()
        }
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
    pub fn get(&self, reg: Byte, size: OpSize, regs_map: &HashMap<&Byte, &&str>) -> Operand {
        match *regs_map[&reg] {
            "ra" => Operand::new(size, self.ra),
            "rb" => Operand::new(size, self.rb),
            "rc" => Operand::new(size, self.rc),
            "rd" => Operand::new(size, self.rd),
            "re" => Operand::new(size, self.re),
            "rf" => Operand::new(size, self.rf),
            "rg" => Operand::new(size, self.rg),
            "rh" => Operand::new(size, self.rh),
            "ri" => Operand::new(size, self.ri),
            "rj" => Operand::new(size, self.rj),
            "rk" => Operand::new(size, self.rk),
            "rl" => Operand::new(size, self.rl),
            "bp" => Operand::new(size, self.bp),
            "sp" => Operand::new(size, self.sp),
            "pc" => Operand::new(size, self.pc),
            "fl" => Operand::new(size, Qword::new(self.fl.bits())),
            _ => unreachable!(),
        }
    }

    pub fn set(&mut self, reg: Byte, val: Operand, regs_map: &HashMap<&Byte, &&str>) {
        match *regs_map[&reg] {
            "ra" => self.ra = val.as_qword(),
            "rb" => self.rb = val.as_qword(),
            "rc" => self.rc = val.as_qword(),
            "rd" => self.rd = val.as_qword(),
            "re" => self.re = val.as_qword(),
            "rf" => self.rf = val.as_qword(),
            "rg" => self.rg = val.as_qword(),
            "rh" => self.rh = val.as_qword(),
            "ri" => self.ri = val.as_qword(),
            "rj" => self.rj = val.as_qword(),
            "rk" => self.rk = val.as_qword(),
            "rl" => self.rl = val.as_qword(),
            "bp" => self.bp = val.as_qword(),
            "sp" => self.sp = val.as_qword(),
            "pc" => self.pc = val.as_qword(),
            "fl" => self.fl = Fl::from_bits_truncate(val.as_qword().get()),
            _ => unreachable!(),
        }
    }
}
