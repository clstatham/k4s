#![allow(clippy::useless_format)]

use std::{cmp::Ordering, collections::HashMap, error::Error, fmt::Display, fs::File, io::Read};

use k4s::*;
use zerocopy::{AsBytes, FromBytes};

pub mod tests;

pub trait Ram {
    fn peek<T: FromBytes>(&self, addr: Qword) -> T;
    fn poke<T: AsBytes>(&mut self, addr: Qword, t: T);
    fn peek_op(&self, size: InstructionSize, addr: Qword) -> Literal;
    fn peek_op_unaligned(&self, size: InstructionSize, addr: Qword) -> Literal;
    fn poke_op(&mut self, addr: Qword, t: Literal);
}

impl Ram for Box<[Byte]> {
    fn peek<T: FromBytes>(&self, addr: Qword) -> T {
        assert_ne!(addr.get(), 0, "null pointer read");
        T::read_from(&self[addr.get() as usize..addr.get() as usize + std::mem::size_of::<T>()])
            .unwrap()
    }
    fn poke<T: AsBytes>(&mut self, addr: Qword, t: T) {
        assert_ne!(addr.get(), 0, "null pointer write");
        self[addr.get() as usize..addr.get() as usize + std::mem::size_of::<T>()]
            .copy_from_slice(t.as_bytes())
    }
    fn peek_op(&self, size: InstructionSize, addr: Qword) -> Literal {
        assert_ne!(addr.get(), 0, "null pointer read");
        assert!(size.in_bytes() > 0, "attempt to read a size of zero");
        assert_eq!(addr.get() % size.in_bytes() as u64, 0, "unaligned read");

        match size {
            InstructionSize::Byte => Literal::Byte(self.peek(addr)),
            InstructionSize::Word => Literal::Word(self.peek(addr)),
            InstructionSize::Dword => Literal::Dword(self.peek(addr)),
            InstructionSize::Qword => Literal::Qword(self.peek(addr)),
            InstructionSize::Unsized => unreachable!(),
        }
        // Operand::new(size, self.peek(addr))
    }
    fn peek_op_unaligned(&self, size: InstructionSize, addr: Qword) -> Literal {
        assert_ne!(addr.get(), 0, "null pointer read");
        assert!(size.in_bytes() > 0, "attempt to read a size of zero");
        match size {
            InstructionSize::Byte => Literal::Byte(self.peek(addr)),
            InstructionSize::Word => Literal::Word(self.peek(addr)),
            InstructionSize::Dword => Literal::Dword(self.peek(addr)),
            InstructionSize::Qword => Literal::Qword(self.peek(addr)),
            InstructionSize::Unsized => unreachable!(),
        }
        // Operand::new(size, self.peek(addr))
    }

    fn poke_op(&mut self, addr: Qword, t: Literal) {
        assert_ne!(addr.get(), 0, "null pointer write");
        assert_eq!(
            addr.get() % t.size().in_bytes() as u64,
            0,
            "unaligned write"
        );
        assert!(t.size().in_bytes() > 0, "attempt to write a size of zero");
        match t {
            Literal::Byte(t) => self.poke(addr, t),
            Literal::Word(t) => self.poke(addr, t),
            Literal::Dword(t) => self.poke(addr, t),
            Literal::Qword(t) => self.poke(addr, t),
        }
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
    Literal(Literal),
    Register(Byte),
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Literal(a) => write!(f, "{}", a),
            Self::Register(a) => {
                let regs = gen_regs();
                let regs_map = regs
                    .into_iter()
                    .map(|(k, v)| (v, k))
                    .collect::<HashMap<_, _>>();
                let reg = regs_map[a];
                write!(f, "{}", reg)
            }
            Self::Unknown(_) => write!(f, "{:?}", self),
        }
    }
}

impl Emulator {
    pub fn new(program: &[u8], memory_size: usize) -> Result<Self, Box<dyn Error>> {
        let mut regs = Regs::default();

        let data = program;
        if &data[..HEADER_MAGIC.len()] != HEADER_MAGIC {
            return Err(EmulationError(format!("Invalid k4s header magic")).into());
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

    #[allow(clippy::borrowed_box)]
    #[allow(clippy::type_complexity)]
    pub fn run(&mut self) -> Result<(), Box<dyn Error>> {
        let ops = gen_bytecodes();
        let ops_map = ops.iter().map(|(op, b)| (b, op)).collect::<HashMap<_, _>>();
        let regs = gen_regs();
        let regs_map = regs
            .iter()
            .map(|(reg, b)| (b, reg))
            .collect::<HashMap<_, _>>();
        let b: &mut [u8; 2] = &mut [0; 2];
        while b
            != ops
                .get(&InstructionVariant {
                    mnemonic: "hlt".into(),
                    args: InstructionArgs::NoArgs,
                    n_args: 0,
                    metadata: MetadataByte::new(InstructionSize::Unsized),
                })
                .unwrap()
        {
            let pc = self.regs.pc;
            b[0] = self.ram.peek(pc);
            b[1] = self.ram.peek((pc.get() + 1).into());
            let op: &InstructionVariant = ops_map.get(b).unwrap();
            let mn = &op.mnemonic;
            let size = op.metadata.op_size();
            let spl = op
                .args
                .basic_str_rep()
                .split_whitespace()
                .collect::<Vec<_>>();
            let mut n = op.n_args + 2;
            let arg1_start = pc.get() as usize + 2;
            let typ1 = self.ram[arg1_start];
            let arg2_start = if typ1 == LIT {
                n += 8;
                arg1_start + 8 + 1
            } else if typ1 == OFFSET {
                n += 9;
                arg1_start + 9 + 1
            } else {
                arg1_start + 1
            };
            let typ2 = self.ram[arg2_start];

            let compute_addend = |regs: &Regs, reg: u8, addend: i64| {
                Literal::new(
                    InstructionSize::Qword,
                    ((regs.get(reg, InstructionSize::Qword, &regs_map).as_qword().get() as i64 + addend)
                        as u64)
                        .into(),
                )
            };

            let parse_lit_2 = |ram: &Box<[Byte]>, arg2: Token| {
                if let Token::Unknown(arg2) = arg2 {
                    if arg2 == LIT {
                        assert_eq!(ram[arg2_start], LIT);
                        return Token::Literal(
                            ram.peek_op_unaligned(size, Qword::new(arg2_start as u64 + 1)),
                        );
                    } else {
                        return Token::Unknown(arg2);
                    }
                }
                arg2
            };
            let parse_lit_1 = |ram: &Box<[Byte]>, arg1: Token| {
                if let Token::Unknown(arg1) = arg1 {
                    if arg1 == LIT {
                        assert_eq!(ram[arg1_start], LIT);
                        return Token::Literal(
                            ram.peek_op_unaligned(size, Qword::new(arg1_start as u64 + 1)),
                        );
                    } else {
                        return Token::Unknown(arg1);
                    }
                }
                arg1
            };
            let parse_reg_addend_2 = |regs: &Regs, ram: &Box<[Byte]>, arg2: Token| {
                if let Token::Unknown(arg2) = arg2 {
                    if arg2 == OFFSET {
                        assert_eq!(ram[arg2_start], OFFSET);
                        let reg = ram.peek(Qword::new(arg2_start as u64 + 1 + 8));
                        let addend = ram.peek(Qword::new(arg2_start as u64 + 1));
                        let val = compute_addend(regs, reg, addend);
                        return Token::Literal(val);
                    } else {
                        return Token::Unknown(arg2);
                    }
                }
                arg2
            };
            let parse_reg_addend_1 = |regs: &Regs, ram: &Box<[Byte]>, arg1: Token| {
                if let Token::Unknown(arg1) = arg1 {
                    if arg1 == OFFSET {
                        assert_eq!(ram[arg1_start], OFFSET);
                        let reg = ram.peek(Qword::new(arg1_start as u64 + 1 + 8));
                        let addend = ram.peek(Qword::new(arg1_start as u64 + 1));
                        let val = compute_addend(regs, reg, addend);
                        return Token::Literal(val);
                    } else {
                        return Token::Unknown(arg1);
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

            let parse1 = |regs: &Regs, ram: &Box<[Byte]>, arg1: Token| {
                let arg1 = parse_reg(arg1);

                let arg1 = parse_reg_addend_1(regs, ram, arg1);
                parse_lit_1(ram, arg1)
            };
            let parse2 = |regs: &Regs, ram: &Box<[Byte]>, arg2: Token| {
                let arg2 = parse_reg(arg2);

                let arg2 = parse_reg_addend_2(regs, ram, arg2);
                parse_lit_2(ram, arg2)
            };

            #[allow(unused_variables)]
            let fmt_arg2 = |arg2| {
                if let Token::Literal(lit) = arg2 {
                    if spl[1].ends_with(']') {
                        format!(
                            "[{}+bp]", //  (=0x{:x})
                            lit.as_qword().get() as isize - self.regs.bp.get() as isize,
                            // self.ram.peek_op(size, lit.as_qword())
                        )
                    } else {
                        format!("$0x{:#x}", lit)
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

            #[allow(unused_variables)]
            let fmt_arg1 = |arg1| {
                if let Token::Literal(lit) = arg1 {
                    if spl[0].ends_with(']') {
                        format!(
                            "[{}+bp]", //  (=0x{:x})
                            lit.as_qword().get() as isize - self.regs.bp.get() as isize,
                            // self.ram.peek_op(size, lit.as_qword()),
                        )
                    } else {
                        format!("$0x{:#x}", lit)
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

            if op.n_args == 2 {
                if typ2 == LIT {
                    n += 8;
                } else if typ2 == OFFSET {
                    n += 9;
                }
            }

            let assign_lvalue_with =
                |regs: &mut Regs,
                 ram: &mut Box<[u8]>,
                 blk: &mut dyn FnMut(
                    &mut Regs,
                    &mut Box<[u8]>,
                    Literal,
                ) -> Result<Literal, Box<EmulationError>>| {
                    let arg1 = parse1(regs, ram, Token::Unknown(typ1));
                    match op.args {
                        InstructionArgs::AdrAdr | InstructionArgs::AdrVal => match arg1 {
                            Token::Register(reg) => {
                                let reg = regs.get(reg, InstructionSize::Qword, &regs_map);
                                let a = ram.peek_op(size, reg.as_qword());
                                let a = blk(regs, ram, a)?;
                                ram.poke_op(reg.as_qword(), a);
                            }
                            Token::Literal(adr) => {
                                let a = ram.peek_op(size, adr.as_qword());
                                let a = blk(regs, ram, a)?;
                                ram.poke_op(adr.as_qword(), a);
                            }
                            t => {
                                return Err::<(), Box<EmulationError>>(
                                    EmulationError(format!(
                                        "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                                    ))
                                    .into(),
                                )
                            }
                        },
                        InstructionArgs::ValVal | InstructionArgs::ValAdr => match arg1 {
                            Token::Register(reg) => {
                                let a = regs.get(reg, InstructionSize::Qword, &regs_map);
                                let a = blk(regs, ram, a)?;
                                regs.set(reg, a, &regs_map);
                            }
                            t => {
                                return Err::<(), Box<EmulationError>>(
                                    EmulationError(format!(
                                        "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                                    ))
                                    .into(),
                                )
                            }
                        },
                        _ => return Ok(()),
                    }
                    Ok(())
                };

            let read2 = |regs: &Regs, ram: &Box<[Byte]>| -> Result<Literal, Box<EmulationError>> {
                let arg = parse2(regs, ram, Token::Unknown(typ2));
                match op.args {
                    InstructionArgs::AdrAdr | InstructionArgs::ValAdr => match arg {
                        Token::Register(reg) => {
                            let a = regs.get(reg, InstructionSize::Qword, &regs_map);
                            let a = ram.peek_op(size, a.as_qword());
                            Ok(a)
                        }
                        Token::Literal(lit) => Ok(ram.peek_op(size, lit.as_qword())),
                        t => Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into()),
                    },
                    InstructionArgs::AdrVal | InstructionArgs::ValVal => match arg {
                        Token::Literal(lit) => Ok(lit),
                        Token::Register(reg) => Ok(regs.get(reg, size, &regs_map)),
                        t => Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into()),
                    },
                    _ => Err(EmulationError(format!(
                        "Tried to access arg 2 of mnemonic `{mn}` that takes 0 or 1 args"
                    ))
                    .into()),
                }
            };

            let read1 = |regs: &Regs, ram: &Box<[Byte]>| -> Result<Literal, Box<EmulationError>> {
                let arg = parse1(regs, ram, Token::Unknown(typ1));
                match op.args {
                    InstructionArgs::AdrVal | InstructionArgs::AdrAdr | InstructionArgs::Adr => match arg {
                        Token::Register(reg) => {
                            let a = regs.get(reg, InstructionSize::Qword, &regs_map);
                            let a = ram.peek_op(size, a.as_qword());
                            Ok(a)
                        }
                        Token::Literal(lit) => Ok(ram.peek_op(size, lit.as_qword())),
                        t => Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into()),
                    },
                    InstructionArgs::ValVal | InstructionArgs::ValAdr | InstructionArgs::Val => match arg {
                        Token::Literal(lit) => Ok(lit),
                        Token::Register(reg) => Ok(regs.get(reg, size, &regs_map)),
                        t => Err(EmulationError(format!(
                            "Invalid token(s) for mnemonic `{mn}`: {t:?}"
                        ))
                        .into()),
                    },
                    _ => Err(EmulationError(format!(
                        "Tried to access arg value of mnemonic `{mn}` that takes no args"
                    ))
                    .into()),
                }
            };

            // println!();
            // println!("{}", self.regs);
            // println!("{:x?}", (self.regs.sp.get()..0x10000.min(self.regs.sp.get() + 0x100)).step_by(8).map(|adr| self.ram.peek::<Qword>((adr).into()).get()).collect::<Vec<_>>());
            // if op.n_args == 0 {
            //     println!("{}", mn);
            // } else if op.n_args == 1 {
            //     println!("{}{} {}", mn, op.metadata.op_size(), fmt_arg1(parse1(&self.regs, &self.ram, Token::Unknown(typ1))));
            // } else {
            //     println!("{}{} {} {}", mn, op.metadata.op_size(), fmt_arg1(parse1(&self.regs, &self.ram, Token::Unknown(typ1))), fmt_arg2(parse2(&self.regs, &self.ram, Token::Unknown(typ2))));
            // }

            match mn.as_str() {
                "hlt" => return Ok(()),
                "nop" => {}
                "mov" => assign_lvalue_with(&mut self.regs, &mut self.ram, &mut |regs, ram, _| {
                    read2(regs, ram)
                })?,
                "push" => {
                    self.push(read1(&self.regs, &self.ram)?.as_qword());
                }
                "pop" => {
                    let a = self.pop();
                    assign_lvalue_with(&mut self.regs, &mut self.ram, &mut |_regs, _ram, _| {
                        Ok(Literal::Qword(a))
                    })?;
                }
                "add" => {
                    assign_lvalue_with(&mut self.regs, &mut self.ram, &mut |regs, ram, lvalue| {
                        Ok(lvalue + read2(regs, ram)?)
                    })?
                }
                "sub" => {
                    assign_lvalue_with(&mut self.regs, &mut self.ram, &mut |regs, ram, lvalue| {
                        Ok(lvalue - read2(regs, ram)?)
                    })?
                }
                "mul" => {
                    assign_lvalue_with(&mut self.regs, &mut self.ram, &mut |regs, ram, lvalue| {
                        Ok(lvalue * read2(regs, ram)?)
                    })?
                }
                "div" => {
                    assign_lvalue_with(&mut self.regs, &mut self.ram, &mut |regs, ram, lvalue| {
                        Ok(lvalue / read2(regs, ram)?)
                    })?
                }
                "mod" => {
                    assign_lvalue_with(&mut self.regs, &mut self.ram, &mut |regs, ram, lvalue| {
                        Ok(lvalue % read2(regs, ram)?)
                    })?
                }
                "and" => {
                    assign_lvalue_with(&mut self.regs, &mut self.ram, &mut |regs, ram, lvalue| {
                        Ok(lvalue & read2(regs, ram)?)
                    })?
                }
                "or" => {
                    assign_lvalue_with(&mut self.regs, &mut self.ram, &mut |regs, ram, lvalue| {
                        Ok(lvalue | read2(regs, ram)?)
                    })?
                }
                "xor" => {
                    assign_lvalue_with(&mut self.regs, &mut self.ram, &mut |regs, ram, lvalue| {
                        Ok(lvalue ^ read2(regs, ram)?)
                    })?
                }
                "shl" => {
                    assign_lvalue_with(&mut self.regs, &mut self.ram, &mut |regs, ram, lvalue| {
                        Ok(lvalue << read2(regs, ram)?)
                    })?
                }
                "shr" => {
                    assign_lvalue_with(&mut self.regs, &mut self.ram, &mut |regs, ram, lvalue| {
                        Ok(lvalue >> read2(regs, ram)?)
                    })?
                }
                "cmp" => {
                    let a = read1(&self.regs, &self.ram)?;
                    let b = read2(&self.regs, &self.ram)?;
                    match a.cmp(&b) {
                        Ordering::Equal => self.regs.fl = Fl::EQ,
                        Ordering::Greater => self.regs.fl = Fl::GT,
                        Ordering::Less => self.regs.fl = Fl::empty(),
                    }
                }
                "jmp" => {
                    self.regs.pc = read1(&self.regs, &self.ram)?.as_qword();
                    continue;
                }
                "jeq" => {
                    if self.regs.fl.eq() {
                        self.regs.pc = read1(&self.regs, &self.ram)?.as_qword();
                        continue;
                    }
                }
                "jne" => {
                    if !self.regs.fl.eq() {
                        self.regs.pc = read1(&self.regs, &self.ram)?.as_qword();
                        continue;
                    }
                }
                "jgt" => {
                    if self.regs.fl.gt() {
                        self.regs.pc = read1(&self.regs, &self.ram)?.as_qword();
                        continue;
                    }
                }
                "jlt" => {
                    if self.regs.fl.lt() {
                        self.regs.pc = read1(&self.regs, &self.ram)?.as_qword();
                        continue;
                    }
                }
                "call" => {
                    self.push((self.regs.pc.get() + n as u64).into());
                    self.regs.pc = read1(&self.regs, &self.ram)?.as_qword();
                    continue;
                }
                "ret" => {
                    self.regs.pc = self.pop();
                    continue;
                }
                "printi" => {
                    let a = read1(&self.regs, &self.ram)?.as_qword();
                    println!("{}", a);
                }
                "printc" => {
                    let a = read1(&self.regs, &self.ram)?.as_byte();
                    print!("{}", std::str::from_utf8(&[a]).unwrap());
                }

                _ => todo!("{:?}", op),
            }

            self.regs.pc.set(self.regs.pc.get() + n as u64);
        }
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut file = File::open("test.k4s")?;
    let mut data = Vec::new();
    file.read_to_end(&mut data)?;
    let mut em = Emulator::new(&data, 0x10000)?;
    em.run()?;
    Ok(())
}
