#![allow(clippy::useless_format)]

use std::{collections::HashMap, error::Error, fmt::Display, fs::File, io::Read};

use k4s::*;
use zerocopy::{AsBytes, FromBytes};


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

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Literal(a) => write!(f, "{}", a),
            Self::Register(a) => {
                let regs = gen_regs();
                let regs_map = regs.into_iter().map(|(k, v)| (v, k)).collect::<HashMap<_, _>>();
                let reg = regs_map[a];
                write!(f, "{}", reg)
            }
            Self::Unknown(_) => write!(f, "{:?}", self),
        }
    }
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
            .set(self.regs.sp.get() - std::mem::size_of::<Qword>() as u64);
        self.ram.poke(self.regs.sp, val);
    }

    fn pop(&mut self) -> Qword {
        let val = self.ram.peek(self.regs.sp);
        self.regs
            .sp
            .set(self.regs.sp.get() + std::mem::size_of::<Qword>() as u64);
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
        while b != *ops.get(&OpVariant { mnemonic: "hlt".into(), op_args: OpArgs::NoArgs }).unwrap() {
            let pc = self.regs.pc;
            b = self.ram.peek(pc);
            let op = ops_map[&b];
            let spl = op.op_args.basic_str_rep().split_whitespace().collect::<Vec<_>>();
            let mn = &op.mnemonic;
            let mut n = spl.len() + 1;
            let arg1_start = pc.get() as usize + 1;
            let typ1 = self.ram[arg1_start];
            let arg2_start = if typ1 == LIT {
                n += 8;
                pc.get() as usize + 1 + 8 + 1
            } else if typ1 == OFFSET {
                n += 9;
                pc.get() as usize + 1 + 9 + 1
            } else {
                pc.get() as usize + 1 + 1
            };
            let typ2 = self.ram[arg2_start];
            

            // println!();

            // println!("{:#?}", self.regs);


            let compute_addend = |reg: u8, addend: i64| {
                ((self.regs.get_qword(reg, &regs_map).get() as i64 + addend) as u64).into()
            };

            let parse_lit_2 = |arg2: Token| {
                if let Token::Unknown(arg2) = arg2 {
                    if arg2 == LIT {
                        assert_eq!(self.ram[arg2_start], LIT);
                        return Token::Literal(self.ram.peek(Qword::new(arg2_start as u64 + 1)));
                    } else {
                        return Token::Unknown(arg2);
                    }
                }
                arg2
            };
            let parse_lit_1 = |arg1: Token| {
                if let Token::Unknown(arg1) = arg1 {
                    if arg1 == LIT {
                        assert_eq!(self.ram[arg1_start], LIT);
                        return Token::Literal(self.ram.peek(Qword::new(arg1_start as u64 + 1)));
                    } else {
                        return Token::Unknown(arg1);
                    }
                }
                arg1
            };
            let parse_reg_addend_2 = |arg2: Token| {
                if let Token::Unknown(arg2) = arg2 {
                    if arg2 == OFFSET {
                        assert_eq!(self.ram[arg2_start], OFFSET);
                        let reg = self.ram.peek(Qword::new(arg2_start as u64 + 1 + 8));
                        let addend = self.ram.peek(Qword::new(arg2_start as u64 + 1));
                        // we can compute the actual value now, since it's an rvalue and we don't have to poke anywhere
                        let val = compute_addend(reg, addend);
                        return Token::Literal(val)
                    } else {
                        return Token::Unknown(arg2)
                    }
                }
                arg2
            };
            let parse_reg_addend_1 = |arg1: Token| {
                if let Token::Unknown(arg1) = arg1 {
                    if arg1 == OFFSET {
                        assert_eq!(self.ram[arg1_start], OFFSET);
                        let reg = self.ram.peek(Qword::new(arg1_start as u64 + 1 + 8));
                        let addend = self.ram.peek(Qword::new(arg1_start as u64 + 1));
                        let val = compute_addend(reg, addend);
                        return Token::Literal(val)
                    } else {
                        return Token::Unknown(arg1)
                    }
                }
                arg1
            };
            let parse_reg = |arg: Token| {
                if let Token::Unknown(arg) = arg {
                    if regs_map.contains_key(&arg) {
                        return Token::Register(arg);
                    } else {
                        return Token::Unknown(arg);
                    }
                }
                arg
            };
            

            let parse1 = |arg1: Token| {
                let arg1 = parse_reg(arg1);

                let arg1 = parse_reg_addend_1(arg1);
                parse_lit_1(arg1)
            };
            let parse2 = |arg2: Token| {
                let arg2 = parse_reg(arg2);

                let arg2 = parse_reg_addend_2(arg2);
                parse_lit_2(arg2)
            };

            let fmt_arg2 = |arg2| {
                if let Token::Literal(lit) = arg2 {
                    if spl[1].ends_with(']') {
                        format!("[${}]", lit)
                    } else {
                        format!("${}", lit)
                    }
                } else if let Token::Register(reg) = arg2 {
                    if spl[1].ends_with(']') {
                        format!("[{}]", regs_map[&reg])
                    } else {
                        format!("{}", regs_map[&reg])
                    }
                } else {
                    unreachable!()
                }
            };

            let fmt_arg1 = |arg1| {
                if let Token::Literal(lit) = arg1 {
                    if spl[0].ends_with(']') {
                        format!("[${}]", lit)
                    } else {
                        format!("${}", lit)
                    }
                } else if let Token::Register(reg) = arg1 {
                    if spl[0].ends_with(']') {
                        format!("[{}]", regs_map[&reg])
                    } else {
                        format!("{}", regs_map[&reg])
                    }
                } else {
                    unreachable!()
                }
            };

            let mut get2args = || {
                let arg1 = parse1(Token::Unknown(typ1));
                if typ2 == LIT {
                    n += 8;
                } else if typ2 == OFFSET {
                    n += 9;
                }
                let arg2 = parse2(Token::Unknown(typ2));
                
                println!("{pc:#x} => {mn} {} {}", fmt_arg1(arg1), fmt_arg2(arg2));
                (
                    arg1,
                    arg2,
                )
            };
            let get1arg = || {
                let arg1 = parse1(Token::Unknown(typ1));
                println!("{pc:#x} => {mn} {}", fmt_arg1(arg1));
                arg1
            };
            // println!("{pc:#x} => {}", op.basic_str_rep());
            match op.basic_str_rep().trim() {
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
                    (Token::Register(a), Token::Literal(b)) => {
                        self.regs.set_qword(a, self.ram.peek(b), &regs_map);
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
                    (Token::Literal(a), Token::Register(b)) => {
                        self.ram.poke(a, self.regs.get_qword(b, &regs_map));
                    }
                    (Token::Literal(a), Token::Literal(b)) => {
                        self.ram.poke(a, b);
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
                        self.ram.poke::<Qword>(
                            self.regs.get_qword(a, &regs_map),
                            self.ram.peek(self.regs.get_qword(b, &regs_map)),
                        );
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        self.ram.poke::<Qword>(self.regs.get_qword(a, &regs_map), self.ram.peek(b));
                    }
                    (Token::Literal(a), Token::Register(b)) => {
                        self.ram.poke::<Qword>(a, self.ram.peek(self.regs.get_qword(b, &regs_map)));
                    }
                    (Token::Literal(a), Token::Literal(b)) => {
                        self.ram.poke::<Qword>(a, self.ram.peek(b));
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
                    Token::Literal(a) => {
                        self.push(self.ram.peek(a));
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
                    Token::Literal(a) => {
                        let val = self.pop();
                        self.ram.poke(a, val);
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
                "add [a] a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.ram.peek::<Qword>(self.regs.get_qword(a, &regs_map));
                        let val = val.get() + self.regs.get_qword(b, &regs_map).get();
                        self.ram.poke::<Qword>(self.regs.get_qword(a, &regs_map), val.into());
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.ram.peek::<Qword>(self.regs.get_qword(a, &regs_map));
                        let val = val.get() + b.get();
                        self.ram.poke::<Qword>(self.regs.get_qword(a, &regs_map), val.into());
                    }
                    (Token::Literal(a), Token::Register(b)) => {
                        let val = self.ram.peek::<Qword>(a);
                        let val = val.get() + self.regs.get_qword(b, &regs_map).get();
                        self.ram.poke::<Qword>(a, val.into());
                    }
                    (Token::Literal(a), Token::Literal(b)) => {
                        let val = self.ram.peek::<Qword>(a);
                        let val = val.get() + b.get();
                        self.ram.poke::<Qword>(a, val.into());
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                },
                "add [a] [a]" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.ram.peek::<Qword>(self.regs.get_qword(a, &regs_map));
                        let val = val.get() + self.ram.peek::<Qword>(self.regs.get_qword(b, &regs_map)).get();
                        self.ram.poke::<Qword>(self.regs.get_qword(a, &regs_map), val.into());
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.ram.peek::<Qword>(self.regs.get_qword(a, &regs_map));
                        let val = val.get() + self.ram.peek::<Qword>(b).get();
                        self.ram.poke::<Qword>(self.regs.get_qword(a, &regs_map), val.into());
                    }
                    (Token::Literal(a), Token::Register(b)) => {
                        let val = self.ram.peek::<Qword>(a);
                        let val = val.get() + self.ram.peek::<Qword>(self.regs.get_qword(b, &regs_map)).get();
                        self.ram.poke::<Qword>(a, val.into());
                    }
                    (Token::Literal(a), Token::Literal(b)) => {
                        let val = self.ram.peek::<Qword>(a);
                        let val = val.get() + self.ram.peek::<Qword>(b).get();
                        self.ram.poke::<Qword>(a, val.into());
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
                "sub [a] a" => match get2args() {
                    (Token::Register(a), Token::Register(b)) => {
                        let val = self.ram.peek::<Qword>(self.regs.get_qword(a, &regs_map));
                        let val = val.get() - self.regs.get_qword(b, &regs_map).get();
                        self.ram.poke::<Qword>(self.regs.get_qword(a, &regs_map), val.into());
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let val = self.ram.peek::<Qword>(self.regs.get_qword(a, &regs_map));
                        let val = val.get() - b.get();
                        self.ram.poke::<Qword>(self.regs.get_qword(a, &regs_map), val.into());
                    }
                    (Token::Literal(a), Token::Register(b)) => {
                        let val = self.ram.peek::<Qword>(a);
                        let val = val.get() - self.regs.get_qword(b, &regs_map).get();
                        self.ram.poke::<Qword>(a, val.into());
                    }
                    (Token::Literal(a), Token::Literal(b)) => {
                        let val = self.ram.peek::<Qword>(a);
                        let val = val.get() - b.get();
                        self.ram.poke::<Qword>(a, val.into());
                    }
                    t => {
                        return Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into())
                    }
                }
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
                        match a.cmp(&b) {
                            std::cmp::Ordering::Equal => self.regs.fl = Fl::EQ,
                            std::cmp::Ordering::Greater => self.regs.fl = Fl::GT,
                            std::cmp::Ordering::Less => self.regs.fl = Fl::empty(),
                        }
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let a = self.regs.get_qword(a, &regs_map).get();
                        let b = b.get();
                        match a.cmp(&b) {
                            std::cmp::Ordering::Equal => self.regs.fl = Fl::EQ,
                            std::cmp::Ordering::Greater => self.regs.fl = Fl::GT,
                            std::cmp::Ordering::Less => self.regs.fl = Fl::empty(),
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
                        match a.cmp(&b) {
                            std::cmp::Ordering::Equal => self.regs.fl = Fl::EQ,
                            std::cmp::Ordering::Greater => self.regs.fl = Fl::GT,
                            std::cmp::Ordering::Less => self.regs.fl = Fl::empty(),
                        }
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let a = self.regs.get_qword(a, &regs_map).get();
                        let b = self.ram.peek::<Qword>(b).get();
                        match a.cmp(&b) {
                            std::cmp::Ordering::Equal => self.regs.fl = Fl::EQ,
                            std::cmp::Ordering::Greater => self.regs.fl = Fl::GT,
                            std::cmp::Ordering::Less => self.regs.fl = Fl::empty(),
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
                        match a.cmp(&b) {
                            std::cmp::Ordering::Equal => self.regs.fl = Fl::EQ,
                            std::cmp::Ordering::Greater => self.regs.fl = Fl::GT,
                            std::cmp::Ordering::Less => self.regs.fl = Fl::empty(),
                        }
                    }
                    (Token::Register(a), Token::Literal(b)) => {
                        let a = self
                            .ram
                            .peek::<Qword>(self.regs.get_qword(a, &regs_map))
                            .get();
                        let b = b.get();
                        match a.cmp(&b) {
                            std::cmp::Ordering::Equal => self.regs.fl = Fl::EQ,
                            std::cmp::Ordering::Greater => self.regs.fl = Fl::GT,
                            std::cmp::Ordering::Less => self.regs.fl = Fl::empty(),
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
