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
use zerocopy::{LittleEndian, U16, U32, U64};

pub const HEADER_MAGIC: &[u8] = b"k4d\x13\x37";
pub const HEADER_ENTRY_POINT: &[u8] = b"ent";
pub const HEADER_END: &[u8] = b"\x69\x69d4k";

pub const LIT: u8 = 0xff;
pub const OFFSET: u8 = 0xfe;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    Byte(Byte),
    Word(Word),
    Dword(Dword),
    Qword(Qword),
}

impl Literal {
    pub fn default_for_size(size: InstructionSize) -> Self {
        match size {
            InstructionSize::Byte => Self::Byte(0),
            InstructionSize::Word => Self::Word(0.into()),
            InstructionSize::Dword => Self::Dword(0.into()),
            InstructionSize::Qword => Self::Qword(0.into()),
            _ => unimplemented!()
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
            Self::Byte(a) => write!(f, "{}", a),
            Self::Word(a) => write!(f, "{}", a),
            Self::Dword(a) => write!(f, "{}", a),
            Self::Qword(a) => write!(f, "{}", a),
        }
    }
}

impl LowerHex for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Byte(a) => write!(f, "{:x}", a),
            Self::Word(a) => write!(f, "{:x}", a),
            Self::Dword(a) => write!(f, "{:x}", a),
            Self::Qword(a) => write!(f, "{:x}", a),
        }
    }
}

impl Literal {
    pub fn new(size: InstructionSize, raw: Qword) -> Self {
        match size {
            InstructionSize::Byte => {
                let b: Byte = (raw.get() & Byte::MAX as u64) as Byte;
                Self::Byte(b)
            }
            InstructionSize::Word => {
                let max: Qword = Word::MAX_VALUE.into();
                let w: u16 = (raw.get() & max.get()) as u16;
                Self::Word(w.into())
            }
            InstructionSize::Dword => {
                let max: Qword = Dword::MAX_VALUE.into();
                let w: u32 = (raw.get() & max.get()) as u32;
                Self::Dword(w.into())
            }
            InstructionSize::Qword => Self::Qword(raw),
            InstructionSize::Unsized => unimplemented!(),
        }
    }

    pub fn from_bits_value(bits: u32, value: u64) -> Self {
        let size = match bits {
            8 => InstructionSize::Byte,
            16 => InstructionSize::Word,
            32 => InstructionSize::Dword,
            64 => InstructionSize::Qword,
            _ => unreachable!(),
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
            Self::Byte(_) => InstructionSize::Byte,
            Self::Word(_) => InstructionSize::Word,
            Self::Dword(_) => InstructionSize::Dword,
            Self::Qword(_) => InstructionSize::Qword,
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

impl Add<Literal> for Literal {
    type Output = Self;
    fn add(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get().wrapping_add(rhs.as_qword().get())).into(),
        )
    }
}

impl Sub<Literal> for Literal {
    type Output = Self;
    fn sub(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get().wrapping_sub(rhs.as_qword().get())).into(),
        )
    }
}

impl Mul<Literal> for Literal {
    type Output = Self;
    fn mul(self, rhs: Literal) -> Self::Output {
        Self::new(
            self.size(),
            (self.as_qword().get().wrapping_mul(rhs.as_qword().get())).into(),
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
    recognize(tuple((tag("%"), many1(alt((alpha1, tag("_"), decimal))))))(i)
}

pub fn data(i: &str) -> IResult<&str, &str> {
    recognize(tuple((tag("@"), many1(alt((alpha1, tag("_"), decimal))))))(i)
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
        Instruction { mnemonic: "hlt", args: (ValidArgs::NOARGS).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Unsized] },
        Instruction { mnemonic: "ret", args: (ValidArgs::NOARGS).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Unsized] },
        Instruction { mnemonic: "mov", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "push", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "pop", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "printi", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "printc", args: (ValidArgs::VAL | ValidArgs::ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte] },
        Instruction { mnemonic: "add", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "sub", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "mul", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "div", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "mod", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "and", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "or", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "xor", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "cmp", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "jmp", args: (ValidArgs::VAL).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Qword] },
        Instruction { mnemonic: "jgt", args: (ValidArgs::VAL).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Qword] },
        Instruction { mnemonic: "jlt", args: (ValidArgs::VAL).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Qword] },
        Instruction { mnemonic: "jeq", args: (ValidArgs::VAL).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Qword] },
        Instruction { mnemonic: "jne", args: (ValidArgs::VAL).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Qword] },
        Instruction { mnemonic: "call", args: (ValidArgs::VAL).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Qword] },
        Instruction { mnemonic: "shl", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
        Instruction { mnemonic: "shr", args: (ValidArgs::VAL_VAL | ValidArgs::VAL_ADR | ValidArgs::ADR_VAL | ValidArgs::ADR_ADR).into_ins_args_vec(), valid_sizes: vec![InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword] },
    ]
}

pub fn gen_bytecodes() -> HashMap<InstructionVariant, [u8; 2]> {
    let mut out = HashMap::new();
    let mut i: u8 = 0;
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
                    [i, metadata.op_size().as_metadata()],
                );
            }
            i = i.checked_add(1).expect("Too many instruction variants!");
        }
    }
    out
}

pub fn gen_regs() -> HashMap<&'static str, u8> {
    [
        "rz", "ra", "rb", "rc", "rd", "re", "rf", "rg", "rh", "ri", "rj", "rk", "rl", "bp", "sp", "pc",
        "fl",
    ]
    .into_iter()
    .enumerate()
    .map(|(i, reg)| (reg, i.try_into().expect("Too many registers! (Why do we need more than 256 registers?)")))
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
    Byte = 0,
    Word = 1,
    Dword = 2,
    Qword = 3,
    Unsized = 4,
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
            Self::Byte => write!(f, " b"),
            Self::Word => write!(f, " w"),
            Self::Dword => write!(f, " d"),
            Self::Qword => write!(f, " q"),
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
            Self::Byte => 1,
            Self::Word => 2,
            Self::Dword => 4,
            Self::Qword => 8,
            Self::Unsized => 0,
        }
    }

    pub fn from_n_bytes(n_bytes: u32) -> Self {
        match n_bytes {
            1 => Self::Byte,
            2 => Self::Word,
            4 => Self::Dword,
            8 => Self::Qword,
            0 => Self::Unsized,
            _ => unimplemented!(),
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
            "ra={:08x} rb={:08x} rc={:08x} rd={:08x} re={:08x} rf={:08x}",
            self.ra, self.rb, self.rc, self.rd, self.re, self.rf
        )?;
        writeln!(
            f,
            "rg={:08x} rh={:08x} ri={:08x} rj={:08x} rk={:08x} rl={:08x}",
            self.rg, self.rh, self.ri, self.rj, self.rk, self.rl
        )?;
        write!(
            f,
            "bp={:08x} sp={:08x} pc={:08x} fl={:08x}",
            self.bp, self.sp, self.pc, self.fl
        )
    }
}

impl Regs {
    pub fn get(&self, reg: Byte, size: InstructionSize, regs_map: &HashMap<&Byte, &&str>) -> Literal {
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
