use std::{
    collections::HashMap,
    fmt::{Display, LowerHex},
    ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub},
};

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, char, one_of, space0, space1},
    combinator::{opt, recognize},
    multi::{many0, many1},
    sequence::{preceded, terminated, tuple},
    IResult,
};
use zerocopy::{LittleEndian, U16, U32, U64, U128};

pub const HEADER_MAGIC: &[u8] = b"k4d\x13\x37";
pub const HEADER_ENTRY_POINT: &[u8] = b"ent";
pub const HEADER_END: &[u8] = b"\x69\x69d4k";

pub const LIT: u8 = 0xff;
pub const OFFSET: u8 = 0xfe;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    U8(Byte),
    U16(Word),
    U32(Dword),
    U64(Qword),
    U128(DQword),
    F32(Dword),
    F64(Qword),
}

impl Literal {
    pub fn default_for_size(size: InstructionSize) -> Self {
        match size {
            InstructionSize::U8 => Self::U8(0),
            InstructionSize::U16 => Self::U16(0.into()),
            InstructionSize::U32 => Self::U32(0.into()),
            InstructionSize::U64 => Self::U64(0.into()),
            InstructionSize::U128 => Self::U128(0.into()),
            _ => unimplemented!(),
        }
    }
}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_qword().get().partial_cmp(&other.as_qword().get())
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_qword().get().cmp(&other.as_qword().get())
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::U8(a) => write!(f, "{}", a),
            Self::U16(a) => write!(f, "{}", a),
            Self::U32(a) => write!(f, "{}", a),
            Self::U64(a) => write!(f, "{}", a),
            Self::U128(a) => write!(f, "{}", a),
            Self::F32(a) => write!(f, "{}", a),
            Self::F64(a) => write!(f, "{}", a),
        }
    }
}

impl LowerHex for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::U8(a) => write!(f, "{:x}", a),
            Self::U16(a) => write!(f, "{:x}", a),
            Self::U32(a) => write!(f, "{:x}", a),
            Self::U64(a) => write!(f, "{:x}", a),
            Self::U128(a) => write!(f, "{:x}", a),
            Self::F32(a) => write!(f, "{:x}", a),
            Self::F64(a) => write!(f, "{:x}", a),
        }
    }
}

impl Literal {
    pub fn new(size: InstructionSize, raw: Qword) -> Self {
        match size {
            InstructionSize::U8 => {
                let b: Byte = (raw.get() & Byte::MAX as u64) as Byte;
                Self::U8(b)
            }
            InstructionSize::U16 => {
                let max: Qword = Word::MAX_VALUE.into();
                let w: u16 = (raw.get() & max.get()) as u16;
                Self::U16(w.into())
            }
            InstructionSize::U32 => {
                let max: Qword = Dword::MAX_VALUE.into();
                let w: u32 = (raw.get() & max.get()) as u32;
                Self::U32(w.into())
            }
            InstructionSize::F32 => {
                let max: Qword = Dword::MAX_VALUE.into();
                let w: u32 = (raw.get() & max.get()) as u32;
                Self::F32(w.into())
            }
            InstructionSize::U64 => Self::U64(raw),
            InstructionSize::F64 => Self::F64(raw),
            InstructionSize::U128 => Self::U128((raw.get() as u128).into()),
            InstructionSize::Unsized => unimplemented!(),
        }
    }

    pub fn from_bits_value_unsigned(bits: u32, value: u64) -> Self {
        let size = match bits {
            1 => InstructionSize::U8,
            8 => InstructionSize::U8,
            16 => InstructionSize::U16,
            24 => InstructionSize::U32, // todo?
            32 => InstructionSize::U32,
            48 => InstructionSize::U64, // todo?
            56 => InstructionSize::U64, // todo?
            64 => InstructionSize::U64,
            96 => InstructionSize::U128, // todo?
            128 => InstructionSize::U128,
            _ => unreachable!("{} bits: {}", bits, value),
        };
        Self::new(size, value.into())
    }

    pub fn display_signed(self, signed: bool) -> String {
        if signed {
            format!("{}", self.as_qword().get() as i64)
        } else {
            format!("{}", self.as_qword().get())
        }
    }

    pub const fn size(self) -> InstructionSize {
        match self {
            Self::U8(_) => InstructionSize::U8,
            Self::U16(_) => InstructionSize::U16,
            Self::U32(_) => InstructionSize::U32,
            Self::U64(_) => InstructionSize::U64,
            Self::U128(_) => InstructionSize::U128,
            Self::F32(_) => InstructionSize::U32,
            Self::F64(_) => InstructionSize::U64,
        }
    }

    pub fn as_byte(self) -> Byte {
        match self {
            Self::U8(a) => a,
            Self::U16(a) => ((a.get() as u64) & Byte::MAX as u64) as Byte,
            Self::U32(a) => ((a.get() as u64) & Byte::MAX as u64) as Byte,
            Self::U64(a) => (a.get() & Byte::MAX as u64) as Byte,
            Self::U128(a) => (a.get() & Byte::MAX as u128) as Byte,
            _ => unimplemented!("{:?} cannot be cast to u8", self),
        }
    }
    pub fn as_word(self) -> Word {
        match self {
            Self::U8(a) => (a as u16).into(),
            Self::U16(a) => a,
            Self::U32(a) => (((a.get() as u64) & Word::MAX_VALUE.get() as u64) as u16).into(),
            Self::U64(a) => (((a.get()) & Word::MAX_VALUE.get() as u64) as u16).into(),
            Self::U128(a) => ((a.get() & Word::MAX_VALUE.get() as u128) as u16).into(),
            _ => unimplemented!("{:?} cannot be cast to u16", self),
        }
    }
    pub fn as_dword(self) -> Dword {
        match self {
            Self::U8(a) => (a as u32).into(),
            Self::U16(a) => (a.get() as u32).into(),
            Self::U32(a) => a,
            Self::F32(a) => a,
            Self::U64(a) => (((a.get()) & Dword::MAX_VALUE.get() as u64) as u32).into(),
            Self::U128(a) => ((a.get() & Dword::MAX_VALUE.get() as u128) as u32).into(),
            _ => unimplemented!("{:?} cannot be cast to u32", self),
        }
    }
    pub fn as_qword(self) -> Qword {
        match self {
            Self::U8(a) => (a as u64).into(),
            Self::U16(a) => (a.get() as u64).into(),
            Self::U32(a) => (a.get() as u64).into(),
            Self::F32(a) => (a.get() as u64).into(),
            Self::U64(a) => a,
            Self::F64(a) => a,
            Self::U128(a) => ((a.get() & Qword::MAX_VALUE.get() as u128) as u64).into(),
        }
    }

    pub fn as_dqword(self) -> DQword {
        match self {
            Self::U8(a) => (a as u128).into(),
            Self::U16(a) => (a.get() as u128).into(),
            Self::U32(a) => (a.get() as u128).into(),
            Self::U64(a) => (a.get() as u128).into(),
            Self::F32(a) => (a.get() as u128).into(),
            Self::F64(a) => (a.get() as u128).into(),
            Self::U128(a) => a,
        }
    }
}

impl Add<Literal> for Literal {
    type Output = Self;
    fn add(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get().add(rhs.as_qword().get())).into(),
        )
    }
}

impl Sub<Literal> for Literal {
    type Output = Self;
    fn sub(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get().sub(rhs.as_qword().get())).into(),
        )
    }
}

impl Mul<Literal> for Literal {
    type Output = Self;
    fn mul(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get().mul(rhs.as_qword().get())).into(),
        )
    }
}

impl Div<Literal> for Literal {
    type Output = Self;
    fn div(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get() / rhs.as_qword().get()).into(),
        )
    }
}

impl Rem<Literal> for Literal {
    type Output = Self;
    fn rem(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get() % rhs.as_qword().get()).into(),
        )
    }
}

impl BitAnd<Literal> for Literal {
    type Output = Self;
    fn bitand(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get() & rhs.as_qword().get()).into(),
        )
    }
}

impl BitOr<Literal> for Literal {
    type Output = Self;
    fn bitor(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get() | rhs.as_qword().get()).into(),
        )
    }
}

impl BitXor<Literal> for Literal {
    type Output = Self;
    fn bitxor(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get() ^ rhs.as_qword().get()).into(),
        )
    }
}

impl Shl<Literal> for Literal {
    type Output = Self;
    fn shl(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get() << rhs.as_qword().get()).into(),
        )
    }
}

impl Shr<Literal> for Literal {
    type Output = Self;
    fn shr(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get() >> rhs.as_qword().get()).into(),
        )
    }
}

bitflags::bitflags! {
    #[derive(PartialEq, Eq, Clone, Copy)]
    pub struct ValidArgs: u16 {
        const NOARGS =   0b1;
        const VAL =      0b10;
        const ADR =      0b100;
        const VAL_VAL =  0b1000;
        const VAL_ADR =  0b10000;
        const ADR_VAL =  0b100000;
        const ADR_ADR =  0b1000000;
    }
}

impl ValidArgs {
    pub fn into_ins_args_vec(self) -> Vec<InstructionArgs> {
        let mut out = vec![];
        if self.contains(Self::NOARGS) {
            out.push(InstructionArgs::NoArgs);
        }
        if self.contains(Self::VAL) {
            out.push(InstructionArgs::Val);
        }
        if self.contains(Self::ADR) {
            out.push(InstructionArgs::Adr);
        }
        if self.contains(Self::VAL_VAL) {
            out.push(InstructionArgs::ValVal);
        }
        if self.contains(Self::VAL_ADR) {
            out.push(InstructionArgs::ValAdr);
        }
        if self.contains(Self::ADR_VAL) {
            out.push(InstructionArgs::AdrVal);
        }
        if self.contains(Self::ADR_ADR) {
            out.push(InstructionArgs::AdrAdr);
        }
        out
    }
}

fn decimal(input: &str) -> IResult<&str, &str> {
    recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(input)
}

fn hexadecimal(input: &str) -> IResult<&str, &str> {
    preceded(
        alt((tag("0x"), tag("0X"))),
        recognize(many1(terminated(
            one_of("0123456789abcdefABCDEF"),
            many0(char('_')),
        ))),
    )(input)
}

pub fn reg(i: &str) -> IResult<&str, &str> {
    alt((
        tag("rz"),
        tag("ra"),
        tag("rb"),
        tag("rc"),
        tag("rd"),
        tag("re"),
        tag("rf"),
        tag("rg"),
        tag("rh"),
        tag("ri"),
        tag("rj"),
        tag("rk"),
        tag("rl"),
        tag("bp"),
        tag("sp"),
        tag("pc"),
        tag("fl"),
    ))(i)
}

pub fn literal(i: &str) -> IResult<&str, &str> {
    recognize(tuple((tag("$"), alt((hexadecimal, decimal)))))(i)
}

pub fn label(i: &str) -> IResult<&str, &str> {
    recognize(tuple((
        tag("%"),
        many1(alt((alpha1, tag("_"), tag("."), decimal))),
    )))(i)
}

pub fn data(i: &str) -> IResult<&str, &str> {
    recognize(tuple((
        tag("@"),
        many1(alt((alpha1, tag("_"), tag("."), decimal))),
    )))(i)
}

pub fn offset(i: &str) -> IResult<&str, &str> {
    recognize(preceded(opt(tag("-")), tuple((decimal, tag("+"), reg))))(i)
}

pub fn val(i: &str) -> IResult<&str, &str> {
    recognize(alt((reg, literal, label, data)))(i)
}

pub fn addr(i: &str) -> IResult<&str, &str> {
    recognize(tuple((tag("["), alt((val, offset)), tag("]"))))(i)
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum InstructionArgs {
    NoArgs,
    Val,
    Adr,
    ValVal,
    ValAdr,
    AdrVal,
    AdrAdr,
}

impl InstructionArgs {
    pub fn parse<'a>(&self, i: &'a str) -> IResult<&'a str, &'a str> {
        match self {
            Self::Val => recognize(val)(i),
            Self::Adr => recognize(addr)(i),
            Self::ValVal => recognize(tuple((val, space1, val)))(i),
            Self::ValAdr => recognize(tuple((val, space1, addr)))(i),
            Self::AdrVal => recognize(tuple((addr, space1, val)))(i),
            Self::AdrAdr => recognize(tuple((addr, space1, addr)))(i),
            Self::NoArgs => Ok((i, i)),
        }
    }

    pub fn n_args(&self) -> usize {
        match self {
            Self::NoArgs => 0,
            Self::Adr | Self::Val => 1,
            _ => 2,
        }
    }

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
}

#[derive(PartialEq, Eq, Hash)]
pub struct Instruction {
    mnemonic: &'static str,
    args: Vec<InstructionArgs>,
    valid_sizes: Vec<InstructionSize>,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct InstructionVariant {
    pub mnemonic: String,
    pub args: InstructionArgs,
    pub n_args: usize,
    pub metadata: MetadataByte,
}

impl InstructionVariant {
    pub fn parse<'a>(&self, i: &'a str) -> IResult<&'a str, &'a str> {
        let args = |i| self.args.parse(i);
        let size = format!("{}", self.metadata.op_size());
        if self.metadata.op_size() == InstructionSize::Unsized {
            let mut parser = recognize(tuple((tag(self.mnemonic.as_str()), space0, args)));
            parser(i)
        } else {
            let mut parser = recognize(tuple((
                tag(self.mnemonic.as_str()),
                space1,
                tag(size.trim().as_bytes()),
                space1,
                args,
            )));
            parser(i)
        }
    }
}

#[rustfmt::skip]
pub fn valid_instructions() -> Vec<Instruction> {
    vec![
        Instruction { mnemonic: "nop", args: (ValidArgs::NOARGS).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Unsized] },
        Instruction { mnemonic: "und", args: (ValidArgs::NOARGS).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Unsized] },
        Instruction { mnemonic: "hlt", args: (ValidArgs::NOARGS).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Unsized] },
        Instruction { mnemonic: "ret", args: (ValidArgs::NOARGS).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Unsized] },
        Instruction { mnemonic: "mov", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "push", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "pop", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "printi", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "printc", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8] },
        Instruction { mnemonic: "add", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "sub", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "mul", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "div", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "sdiv", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "mod", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128] },
        Instruction { mnemonic: "smod", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128] },
        Instruction { mnemonic: "and", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "or", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "xor", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "cmp", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128] },
        Instruction { mnemonic: "scmp", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128] },
        Instruction { mnemonic: "fcmp", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128, InstructionSize::F32, InstructionSize::F64] },
        Instruction { mnemonic: "jmp", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jgt", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jge", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jlt", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jle", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jeq", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jne", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "juno", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "junoeq", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "junone", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "junolt", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "junogt", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "junole", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "junoge", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jord", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jordeq", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jordne", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jordlt", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jordgt", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jordle", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "jordge", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "call", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U64] },
        Instruction { mnemonic: "shl", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128] },
        Instruction { mnemonic: "shr", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128] },
        Instruction { mnemonic: "sshr", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128] },
        Instruction { mnemonic: "sext", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::U8, InstructionSize::U16, InstructionSize::U32, InstructionSize::U64, InstructionSize::U128] },
    ]
}

pub fn gen_bytecodes() -> HashMap<InstructionVariant, [u8; 3]> {
    let mut out = HashMap::new();
    let mut i: u16 = 0;
    for op in valid_instructions() {
        for variant in op.args {
            let n_args = variant.n_args();
            for operand_size in &op.valid_sizes {
                let metadata = MetadataByte::new(*operand_size);
                out.insert(
                    InstructionVariant {
                        mnemonic: op.mnemonic.to_owned(),
                        args: variant,
                        n_args,
                        metadata,
                    },
                    [i.to_le_bytes()[0], i.to_le_bytes()[1], metadata.op_size().as_metadata()],
                );
            }
            i = i.checked_add(1).expect("Too many instruction variants!");
        }
    }
    out
}

pub fn gen_regs() -> HashMap<&'static str, u8> {
    [
        "rz", "ra", "rb", "rc", "rd", "re", "rf", "rg", "rh", "ri", "rj", "rk", "rl", "bp", "sp",
        "pc", "fl",
    ]
    .into_iter()
    .enumerate()
    .map(|(i, reg)| {
        (
            reg,
            i.try_into()
                .expect("Too many registers! (Why do we need more than 256 registers?)"),
        )
    })
    .collect()
}

pub type DQword = U128<LittleEndian>;
pub type Qword = U64<LittleEndian>;
pub type Dword = U32<LittleEndian>;
pub type Word = U16<LittleEndian>;
pub type Byte = u8;

bitflags::bitflags! {
    #[derive(Debug, Default, Clone, Copy)]
    #[repr(transparent)]
    pub struct Fl: u64 {
        const EQ = 0b01;
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum InstructionSize {
    U8 = 0,
    U16 = 1,
    U32 = 2,
    U64 = 3,
    U128 = 4, // double-quad-word??? (dairy queen word??????)
    F32 = 16,
    F64 = 17,
    Unsized = 100,
}

impl PartialOrd for InstructionSize {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.in_bytes().partial_cmp(&other.in_bytes())
    }
}

impl Ord for InstructionSize {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.in_bytes().cmp(&other.in_bytes())
    }
}

impl Display for InstructionSize {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::U8 => write!(f, " u8"),
            Self::U16 => write!(f, " u16"),
            Self::U32 => write!(f, " u32"),
            Self::U64 => write!(f, " u64"),
            Self::U128 => write!(f, " u128"),
            Self::F32 => write!(f, " f32"),
            Self::F64 => write!(f, " f64"),
            Self::Unsized => write!(f, ""),
        }
    }
}

impl InstructionSize {
    pub fn as_metadata(self) -> u8 {
        self as u8
    }

    pub fn in_bytes(self) -> usize {
        match self {
            Self::U8 => 1,
            Self::U16 => 2,
            Self::U32 => 4,
            Self::U64 => 8,
            Self::U128 => 16,
            Self::F32 => 4,
            Self::F64 => 8,
            Self::Unsized => 0,
        }
    }

    pub fn from_n_bytes_unsigned(n_bytes: u32) -> Self {
        match n_bytes {
            1 => Self::U8,
            2 => Self::U16,
            3 => Self::U32, // todo?
            4 => Self::U32,
            6 => Self::U64, // todo?
            7 => Self::U64, // todo?
            8 => Self::U64,
            12 => Self::U128, // todo?
            16 => Self::U128,
            0 => Self::Unsized,
            n => unimplemented!("{:?} bytes", n),
        }
    }

    pub fn from_n_bits_unsigned(n_bits: u32) -> Self {
        match n_bits {
            1 => Self::U8,
            8 => Self::U8,
            16 => Self::U16,
            24 => Self::U32, // todo?
            32 => Self::U32,
            48 => Self::U64, // todo?
            56 => Self::U64, // todo?
            64 => Self::U64,
            96 => Self::U128, // todo?
            128 => Self::U128,
            0 => Self::Unsized,
            n => unimplemented!("{:?} bits", n),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct MetadataByte(InstructionSize);

impl MetadataByte {
    pub fn new(operand_size: InstructionSize) -> Self {
        Self(operand_size) // todo: more options
    }

    pub fn op_size(self) -> InstructionSize {
        self.0
    }
}

#[derive(Default)]
pub struct Rz;

#[repr(C)]
#[derive(Default)]
pub struct Regs {
    pub rz: Rz,
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

impl Display for Regs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "ra={:016x} rb={:016x} rc={:016x} rd={:016x} re={:016x} rf={:016x}",
            self.ra, self.rb, self.rc, self.rd, self.re, self.rf
        )?;
        writeln!(
            f,
            "rg={:016x} rh={:016x} ri={:016x} rj={:016x} rk={:016x} rl={:016x}",
            self.rg, self.rh, self.ri, self.rj, self.rk, self.rl
        )?;
        write!(
            f,
            "bp={:016x} sp={:016x} pc={:016x} fl={:016x}",
            self.bp, self.sp, self.pc, self.fl
        )
    }
}

impl Regs {
    pub fn get(
        &self,
        reg: Byte,
        size: InstructionSize,
        regs_map: &HashMap<&Byte, &&str>,
    ) -> Literal {
        match *regs_map[&reg] {
            "rz" => Literal::new(size, 0.into()),
            "ra" => Literal::new(size, self.ra),
            "rb" => Literal::new(size, self.rb),
            "rc" => Literal::new(size, self.rc),
            "rd" => Literal::new(size, self.rd),
            "re" => Literal::new(size, self.re),
            "rf" => Literal::new(size, self.rf),
            "rg" => Literal::new(size, self.rg),
            "rh" => Literal::new(size, self.rh),
            "ri" => Literal::new(size, self.ri),
            "rj" => Literal::new(size, self.rj),
            "rk" => Literal::new(size, self.rk),
            "rl" => Literal::new(size, self.rl),
            "bp" => Literal::new(size, self.bp),
            "sp" => Literal::new(size, self.sp),
            "pc" => Literal::new(size, self.pc),
            "fl" => Literal::new(size, Qword::new(self.fl.bits())),
            _ => unreachable!(),
        }
    }

    pub fn set(&mut self, reg: Byte, val: Literal, regs_map: &HashMap<&Byte, &&str>) {
        match *regs_map[&reg] {
            "rz" => panic!("Attempt to assign to rz"),
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
