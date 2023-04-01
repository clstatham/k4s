use std::{collections::HashMap, error::Error, fmt::Display, fs::File, io::Read};

use k4s::*;
use zerocopy::{AsBytes, FromBytes, LittleEndian, U16, U32, U64};

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

pub trait Ram {
    fn peek<T: FromBytes>(&self, addr: Qword) -> T;
    fn poke<T: AsBytes>(&mut self, addr: Qword, t: T);
}

impl Ram for Box<[Byte]> {
    fn peek<T: FromBytes>(&self, addr: Qword) -> T {
        T::read_from(&self[addr.get() as usize..addr.get() as usize + std::mem::size_of::<T>()])
            .unwrap()
    }
    fn poke<T: AsBytes>(&mut self, addr: Qword, t: T) {
        self[addr.get() as usize..addr.get() as usize + std::mem::size_of::<T>()]
            .copy_from_slice(t.as_bytes())
    }
}

#[derive(Debug)]
pub struct EmulationError(String);
impl Display for EmulationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
impl Error for EmulationError {}

pub struct Emulator {
    pub regs: Regs,
    pub ram: Box<[Byte]>,
}

#[derive(Clone, Copy, Debug)]
pub enum Token {
    Unknown(Byte),
    Literal(Qword),
    Register(Byte),
}

impl Token {
    pub fn unwrap_literal(self) -> Qword {
        match self {
            Self::Literal(v) => v,
            _ => panic!("unwrap_literal() called on unknown or register token"),
        }
    }
    pub fn unwrap_register(self) -> Byte {
        match self {
            Self::Register(r) => r,
            _ => panic!("unwrap_register() called on unknown or literal token"),
        }
    }
}

impl Emulator {
    pub fn new(program_path: &str, memory_size: usize) -> Result<Self, Box<dyn Error>> {
        let mut regs = Regs::default();

        let mut file = File::open(program_path)?;
        let mut data = Vec::new();
        file.read_to_end(&mut data)?;
        if &data[..HEADER_MAGIC.len()] != HEADER_MAGIC {
            return Err(EmulationError(format!("Invalid k4s magic")).into());
        }
        let data = &data[HEADER_MAGIC.len()..];
        if &data[..HEADER_ENTRY_POINT.len()] != HEADER_ENTRY_POINT {
            return Err(EmulationError(format!("Invalid k4s entry point magic")).into());
        }
        let data = &data[HEADER_ENTRY_POINT.len()..];
        let entry_point = Qword::from_bytes([
            data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7],
        ]);
        let data = &data[8..];

        if &data[..HEADER_END.len()] != HEADER_END {
            return Err(EmulationError(format!("Invalid k4s header end magic")).into());
        }
        let data = &data[HEADER_END.len()..];

        let mut ram = vec![0u8; memory_size].into_boxed_slice();
        ram[entry_point.get() as usize..entry_point.get() as usize + data.len()]
            .copy_from_slice(data);

        regs.sp = Qword::new(memory_size as u64);
        regs.pc = entry_point;

        Ok(Self { regs, ram })
    }

    fn push(&mut self, val: Qword) {
        self.regs
            .sp
            .set(self.regs.sp.get() - core::mem::size_of::<Qword>() as u64);
        self.ram.poke(self.regs.sp, val);
    }

    fn pop(&mut self) -> Qword {
        let val = self.ram.peek(self.regs.sp);
        self.regs
            .sp
            .set(self.regs.sp.get() + core::mem::size_of::<Qword>() as u64);
        val
    }

    pub fn run(&mut self) -> Result<(), Box<dyn Error>> {
        let ops = gen_bytecodes();
        let ops_map = ops.iter().map(|(op, b)| (b, op)).collect::<HashMap<_, _>>();
        let regs = gen_regs();
        let regs_map = regs
            .iter()
            .map(|(reg, b)| (b, reg))
            .collect::<HashMap<_, _>>();
        let mut b: Byte = 0;
        while b != ops["hlt"] {
            let pc = self.regs.pc;
            b = self.ram.peek(pc);
            let op = ops_map[&b];
            let spl = op.split_whitespace().collect::<Vec<_>>();
            let mn = spl[0];
            let mut n = spl.len();
            let data = &self.ram[pc.get() as usize..pc.get() as usize + n];
            if *data.last().unwrap() == LIT {
                n += core::mem::size_of::<Qword>();
            }

            let parse_lit_2 = |arg2: Token| {
                if let Token::Unknown(arg2) = arg2 {
                    if arg2 == LIT {
                        assert_eq!(self.ram[self.regs.pc.get() as usize + 2], LIT);
                        return Token::Literal(self.ram.peek(Qword::new(self.regs.pc.get() + 3)));
                    } else {
                        return Token::Unknown(arg2);
                    }
                }
                return arg2;
            };
            let parse_lit_1 = |arg1: Token| {
                if let Token::Unknown(arg1) = arg1 {
                    if arg1 == LIT {
                        assert_eq!(self.ram[self.regs.pc.get() as usize + 1], LIT);
                        return Token::Literal(self.ram.peek(Qword::new(self.regs.pc.get() + 2)));
                    } else {
                        return Token::Unknown(arg1);
                    }
                }
                return arg1;
            };
            let parse_reg = |arg: Token| {
                if let Token::Unknown(arg) = arg {
                    if regs_map.contains_key(&arg) {
                        return Token::Register(arg);
                    } else {
                        return Token::Unknown(arg);
                    }
                }
                return arg;
            };

            let parse1 = |arg1: Token| {
                let arg1 = parse_reg(arg1);
                let arg1 = parse_lit_1(arg1);

                arg1
            };
            let parse2 = |arg2: Token| {
                let arg2 = parse_reg(arg2);
                let arg2 = parse_lit_2(arg2);

                arg2
            };

            let get2args = || {
                assert_eq!(data.len(), 3);
                (
                    parse1(Token::Unknown(data[1])),
                    parse2(Token::Unknown(data[2])),
                )
            };
            let get1arg = || parse1(Token::Unknown(data[1]));
            // println!("{pc:#x} => {op}");
            match op.as_str() {
                "mov a a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        self.regs
                            .set_qword(a, self.regs.get_qword(b, &regs_map), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        self.regs.set_qword(a, b, &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "mov a [a]" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        self.regs.set_qword(
                            a,
                            self.ram.peek(self.regs.get_qword(b, &regs_map)),
                            &regs_map,
                        );
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "mov [a] a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        self.ram.poke(
                            self.regs.get_qword(a, &regs_map),
                            self.regs.get_qword(b, &regs_map),
                        );
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        self.ram.poke(self.regs.get_qword(a, &regs_map), b);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "mov [a] [a]" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        self.ram.poke(
                            self.regs.get_qword(a, &regs_map),
                            self.ram.peek::<Byte>(self.regs.get_qword(b, &regs_map)),
                        );
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "push a" => match get1arg() {
                    Token::Literal(a) => self.push(a),
                    Token::Register(a) => self.push(self.regs.get_qword(a, &regs_map)),
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "push [a]" => match get1arg() {
                    Token::Register(a) => {
                        self.push(self.ram.peek(self.regs.get_qword(a, &regs_map)))
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "pop a" => match get1arg() {
                    Token::Register(a) => {
                        let val = self.pop();
                        self.regs.set_qword(a, val, &regs_map)
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "pop [a]" => match get1arg() {
                    Token::Register(a) => {
                        let val = self.pop();
                        self.ram.poke(self.regs.get_qword(a, &regs_map), val)
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "add a a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            + self.regs.get_qword(b, &regs_map).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get() + b.get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "add a [a]" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            + self
                                .ram
                                .peek::<Qword>(self.regs.get_qword(b, &regs_map))
                                .get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            + self.ram.peek::<Qword>(b).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "sub a a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            - self.regs.get_qword(b, &regs_map).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get() - b.get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "sub a [a]" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            - self
                                .ram
                                .peek::<Qword>(self.regs.get_qword(b, &regs_map))
                                .get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            - self.ram.peek::<Qword>(b).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "mul a a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            * self.regs.get_qword(b, &regs_map).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get() * b.get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "mul a [a]" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            * self
                                .ram
                                .peek::<Qword>(self.regs.get_qword(b, &regs_map))
                                .get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            * self.ram.peek::<Qword>(b).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "div a a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            / self.regs.get_qword(b, &regs_map).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get() / b.get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "div a [a]" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            / self
                                .ram
                                .peek::<Qword>(self.regs.get_qword(b, &regs_map))
                                .get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            / self.ram.peek::<Qword>(b).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "mod a a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            % self.regs.get_qword(b, &regs_map).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get() % b.get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "mod a [a]" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            % self
                                .ram
                                .peek::<Qword>(self.regs.get_qword(b, &regs_map))
                                .get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            % self.ram.peek::<Qword>(b).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "and a a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            & self.regs.get_qword(b, &regs_map).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get() & b.get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "and a [a]" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            & self
                                .ram
                                .peek::<Qword>(self.regs.get_qword(b, &regs_map))
                                .get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            & self.ram.peek::<Qword>(b).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "or a a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            | self.regs.get_qword(b, &regs_map).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get() | b.get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "or a [a]" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            | self
                                .ram
                                .peek::<Qword>(self.regs.get_qword(b, &regs_map))
                                .get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            | self.ram.peek::<Qword>(b).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "xor a a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            ^ self.regs.get_qword(b, &regs_map).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get() ^ b.get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "xor a [a]" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            ^ self
                                .ram
                                .peek::<Qword>(self.regs.get_qword(b, &regs_map))
                                .get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            ^ self.ram.peek::<Qword>(b).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "shl a a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            << self.regs.get_qword(b, &regs_map).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get() << b.get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "shr a a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get()
                            >> self.regs.get_qword(b, &regs_map).get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.regs.get_qword(a, &regs_map).get() >> b.get();
                        self.regs.set_qword(a, val.into(), &regs_map);
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "printi a" => match get1arg() {
                    Token::Register(a) => {
                        println!("{}", self.regs.get_qword(a, &regs_map));
                    }
                    Token::Literal(a) => {
                        println!("{}", a.get())
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "printi [a]" => match get1arg() {
                    Token::Register(a) => {
                        println!(
                            "{}",
                            self.ram.peek::<Qword>(self.regs.get_qword(a, &regs_map))
                        );
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "printc a" => match get1arg() {
                    Token::Literal(a) => {
                        let a = a.get();
                        print!("{}", String::from_utf8(vec![a.try_into()?]).unwrap())
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "printc [a]" => match get1arg() {
                    Token::Register(a) => {
                        print!(
                            "{}",
                            String::from_utf8(vec![self
                                .ram
                                .peek::<Byte>(self.regs.get_qword(a, &regs_map))])
                            .unwrap()
                        );
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "jmp a" => match get1arg() {
                    Token::Literal(a) => {
                        self.regs.pc = a;
                        continue;
                    }
                    Token::Register(a) => {
                        self.regs.pc = self.regs.get_qword(a, &regs_map);
                        continue;
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "cmp a a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let a = self.regs.get_qword(a, &regs_map).get();
                        let b = self.regs.get_qword(b, &regs_map).get();
                        if a == b {
                            self.regs.fl = Fl::EQ;
                        } else if a > b {
                            self.regs.fl = Fl::GT;
                        } else {
                            self.regs.fl = Fl::empty();
                        }
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let a = self.regs.get_qword(a, &regs_map).get();
                        let b = b.get();
                        if a == b {
                            self.regs.fl = Fl::EQ;
                        } else if a > b {
                            self.regs.fl = Fl::GT;
                        } else {
                            self.regs.fl = Fl::empty();
                        }
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "cmp a [a]" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let a = self.regs.get_qword(a, &regs_map).get();
                        let b = self
                            .ram
                            .peek::<Qword>(self.regs.get_qword(b, &regs_map))
                            .get();
                        if a == b {
                            self.regs.fl = Fl::EQ;
                        } else if a > b {
                            self.regs.fl = Fl::GT;
                        } else {
                            self.regs.fl = Fl::empty();
                        }
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let a = self.regs.get_qword(a, &regs_map).get();
                        let b = self.ram.peek::<Qword>(b).get();
                        if a == b {
                            self.regs.fl = Fl::EQ;
                        } else if a > b {
                            self.regs.fl = Fl::GT;
                        } else {
                            self.regs.fl = Fl::empty();
                        }
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "cmp [a] a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let a = self
                            .ram
                            .peek::<Qword>(self.regs.get_qword(a, &regs_map))
                            .get();
                        let b = self.regs.get_qword(b, &regs_map).get();
                        if a == b {
                            self.regs.fl = Fl::EQ;
                        } else if a > b {
                            self.regs.fl = Fl::GT;
                        } else {
                            self.regs.fl = Fl::empty();
                        }
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let a = self
                            .ram
                            .peek::<Qword>(self.regs.get_qword(a, &regs_map))
                            .get();
                        let b = b.get();
                        if a == b {
                            self.regs.fl = Fl::EQ;
                        } else if a > b {
                            self.regs.fl = Fl::GT;
                        } else {
                            self.regs.fl = Fl::empty();
                        }
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "jeq a" => match get1arg() {
                    Token::Literal(a) => {
                        if self.regs.fl.eq() {
                            self.regs.pc = a;
                            continue;
                        }
                    }
                    Token::Register(a) => {
                        if self.regs.fl.eq() {
                            self.regs.pc = self.regs.get_qword(a, &regs_map);
                            continue;
                        }
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "jne a" => match get1arg() {
                    Token::Literal(a) => {
                        if !self.regs.fl.eq() {
                            self.regs.pc = a;
                            continue;
                        }
                    }
                    Token::Register(a) => {
                        if !self.regs.fl.eq() {
                            self.regs.pc = self.regs.get_qword(a, &regs_map);
                            continue;
                        }
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "jgt a" => match get1arg() {
                    Token::Literal(a) => {
                        if self.regs.fl.gt() {
                            self.regs.pc = a;
                            continue;
                        }
                    }
                    Token::Register(a) => {
                        if self.regs.fl.gt() {
                            self.regs.pc = self.regs.get_qword(a, &regs_map);
                            continue;
                        }
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "jlt a" => match get1arg() {
                    Token::Literal(a) => {
                        if self.regs.fl.lt() {
                            self.regs.pc = a;
                            continue;
                        }
                    }
                    Token::Register(a) => {
                        if self.regs.fl.lt() {
                            self.regs.pc = self.regs.get_qword(a, &regs_map);
                            continue;
                        }
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "call a" => match get1arg() {
                    Token::Literal(a) => {
                        self.push((self.regs.pc.get() + n as u64).into());
                        self.push(self.regs.rg);
                        self.push(self.regs.rh);
                        self.push(self.regs.ri);
                        self.push(self.regs.rj);
                        self.push(self.regs.rk);
                        self.push(self.regs.rl);
                        self.regs.pc = a;
                        continue;
                    }
                    Token::Register(a) => {
                        self.push((self.regs.pc.get() + n as u64).into());
                        self.push(self.regs.rg);
                        self.push(self.regs.rh);
                        self.push(self.regs.ri);
                        self.push(self.regs.rj);
                        self.push(self.regs.rk);
                        self.push(self.regs.rl);
                        self.regs.pc = self.regs.get_qword(a, &regs_map);
                        continue;
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "ret" => {
                    self.regs.rl = self.pop();
                    self.regs.rk = self.pop();
                    self.regs.rj = self.pop();
                    self.regs.ri = self.pop();
                    self.regs.rh = self.pop();
                    self.regs.rg = self.pop();
                    self.regs.pc = self.pop();
                    continue;
                }
                "nop" => {}
                "hlt" => return Ok(()),
                op => return Err(EmulationError(format!("Unknown op: {op}")).into()),
            }

            self.regs.pc.set(self.regs.pc.get() + n as u64);
        }
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut em = Emulator::new("test.k4s", 0x10000)?;
    em.run()?;
    Ok(())
}
