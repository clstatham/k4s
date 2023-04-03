// #![allow(unused_variables)]

use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fmt::Write,
    path::Path,
};

use k4s::{Literal, OpSize};
use llvm_ir::{
    function::Parameter,
    terminator::{Ret, Br, CondBr},
    Constant, Instruction, Module, Name, Operand, Terminator, Type, IntPredicate,
};

pub struct Parser {
    module: Module,
    output: String,
}

#[derive(Clone)]
pub struct Ssa {
    pub name: Name,
    pub storage: Storage,
    pub size: OpSize,
}

impl Ssa {
    pub fn new(storage: Storage, size: OpSize, name: Name) -> Self {
        Self { name, storage, size }
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
    BpOffset { off: isize, pointer: Pointer },
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
            Self::Label { name } => return name.to_owned(),
            Self::Constant { value, signed } => {
                return format!("${}", value.display_signed(*signed))
            }
            Self::BpOffset { off, pointer: _ } => {
                return format!("[{off}+bp]");
            }
        };
        s.to_owned()
    }
}

pub struct RegPool {
    pub used_regs: HashMap<Name, Ssa>,
    pub avail_regs: HashSet<Storage>,
    pub rel_sp: isize,
}
impl RegPool {
    pub fn new(params: Vec<Parameter>, output: &mut impl Write) -> Self {
        let mut this = Self {
            rel_sp: 0,
            used_regs: HashMap::new(),
            avail_regs: ALL_REGS.iter().cloned().collect(),
        };
        for (param, reg) in params.iter().zip(
            [
                Storage::Rg,
                Storage::Rh,
                Storage::Ri,
                Storage::Rj,
                Storage::Rk,
                Storage::Rl,
            ][..params.len()]
                .iter(),
        ) {
            
            let stack_ptr = this.push_stack(param.name.to_owned(), op_size(&param.ty));
            writeln!(output, "; {} <= {}", stack_ptr.name, reg.display()).unwrap();
            writeln!(output, "    mov{} {} {}", stack_ptr.size, stack_ptr.storage.display(), reg.display()).unwrap();
            // this.avail_regs.remove(reg);
            // this.used_regs
            //     .insert(param.name.to_owned(), Ssa::new(reg.clone(), op_size(&param.ty), param.name.to_owned()));
        }
        this
    }

    pub fn reinsert(&mut self, ssa: Ssa) {
        assert!(self.used_regs.remove(&ssa.name).is_some());
        assert!(self.avail_regs.insert(ssa.storage));
    }

    pub fn push_stack(&mut self, name: Name, size: OpSize) -> Ssa {
        self.rel_sp -= Pointer::size().in_bytes() as isize;
        self.rel_sp -= self.rel_sp % Pointer::size().in_bytes() as isize; // align down
        let ssa = Ssa::new(
            Storage::BpOffset {
                off: self.rel_sp,
                pointer: Pointer { pointee_size: size }
            },
            Pointer::size(),
            name.clone(),
        );
        self.used_regs.insert(name, ssa.clone());
        self.avail_regs.remove(&ssa.storage);

        ssa
    }

    pub fn get(&self, name: Name) -> Option<Ssa> {
        self.used_regs.get(&name).cloned()
    }

    pub fn constant(&mut self, name: Name, value: Literal, signed: bool) -> Ssa {
        let ssa = Ssa::new(Storage::Constant { value, signed }, value.size(), name.clone());
        self.used_regs.insert(name, ssa.clone());
        self.avail_regs.remove(&ssa.storage);
        ssa
    }

    pub fn label(&mut self, func_name: String, name: String) -> Ssa {
        let name = name.strip_prefix('%').unwrap_or(&name);
        let name = format!("{func_name}_{name}");
        let name = Name::Name(name.into());
        self.used_regs.get(&name).cloned().unwrap_or_else(|| {
            let ssa = Ssa::new(Storage::Label { name: name.clone().to_string() }, OpSize::Qword, name.clone());
            self.used_regs.insert(name.clone(), ssa.clone());
            self.avail_regs.remove(&ssa.storage);
            ssa
        })
    }

    pub fn get_or_push_stack(&mut self, name: Name, size: OpSize) -> Ssa {
        // self.get(name.clone())
        //     .unwrap_or_else(|| self.push_stack(name, output))
        if let Some(ssa) = self.get(name.clone()) {
            ssa
        } else {
            self.push_stack(name, size)
        }        
    }

    #[must_use = "This returns None if there aren't any available registers!"]
    pub fn get_unused(&mut self, size: OpSize, name: Name) -> Option<Ssa> {
        for reg in ALL_REGS.iter() {
        
            if self.avail_regs.remove(reg) {
                let ssa = Ssa::new(reg.clone(), size, name.clone());
                self.used_regs.insert(name, ssa.clone());
                return Some(ssa);
            }
        }
        None
    }

    pub fn pick_for_me(&mut self, name: Name, size: OpSize) -> Ssa {
        self.get(name.clone())
            .or_else(|| self.get_unused(size, name.clone()))
            .or_else(|| Some(self.push_stack(name, size))).unwrap()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct Pointer {
    pointee_size: OpSize,
}

impl Pointer {
    pub const fn size() -> OpSize {
        OpSize::Qword
    }

    pub fn pointee_size(&self) -> OpSize {
        self.pointee_size
    }
}

#[inline]
pub fn op_size(typ: &Type) -> OpSize {
    match typ {
        Type::IntegerType { bits } => match *bits {
            1 => OpSize::Byte, // boolean
            8 => OpSize::Byte,
            16 => OpSize::Word,
            32 => OpSize::Dword,
            64 => OpSize::Qword,
            x => unreachable!("integer bits {}", x),
        },
        Type::PointerType {  .. } => Pointer::size(),
        _ => todo!(),
    }
}

// macro_rules! parse_operand {
pub fn parse_operand(op: &Operand, pool: &mut RegPool, assert_exists: bool) -> Ssa {
    match op {
        Operand::ConstantOperand(con) => {
            let con = &**con;
            let (value, signed) = match con {
                Constant::Int { bits, value } => (Literal::from_bits_value(*bits, *value), true),
                x => todo!("{}", x),
            };
            pool.constant(Name::Name("constant".to_owned().into()), value, signed)
        }
        Operand::LocalOperand { name, ty } => {
            if assert_exists {
                pool.get(name.to_owned()).unwrap()
            } else {
                pool.get_or_push_stack(name.to_owned(), op_size(ty))
            }
        }
        x => todo!("{}", x),
    }
}

pub fn load(dst: Ssa, src: Ssa, align: OpSize, pool: &mut RegPool, output: &mut impl Write) -> Result<(), Box<dyn Error>> {
    match (src.storage, dst.storage) {
        (Storage::BpOffset { off: src_off, pointer: src_pointer }, Storage::BpOffset { off: dst_off, pointer: dst_pointer }) => {
            let tmp = pool.get_unused(Pointer::size(), Name::Name("tmp1".to_owned().into())).unwrap();
            writeln!(output, "    mov{} {} [{}+bp]", Pointer::size(), tmp.storage.display(), src_off)?;
            writeln!(output, "    mov{} [{}+bp] [{}]", align, dst_off, tmp.storage.display())?;
            pool.reinsert(tmp);
        }
        (Storage::BpOffset { off: src_off, pointer: _src_pointer }, dst_storage) => {
            let tmp = pool.get_unused(Pointer::size(), Name::Name("tmp".to_owned().into())).unwrap();
            writeln!(output, "    mov{} {} [{}+bp]", Pointer::size(), tmp.storage.display(), src_off)?;
            writeln!(output, "    mov{} {} [{}]", align, dst_storage.display(), tmp.storage.display())?;
            pool.reinsert(tmp);
        }
        (src_storage, Storage::BpOffset { off: dst_off, pointer: dst_pointer }) => {
            writeln!(output, "    mov{} [{}+bp] [{}]", align, dst_off, src_storage.display())?;
        }
        (src_storage, dst_storage) => {
            writeln!(output, "    mov{} {} [{}]", align, dst_storage.display(), src_storage.display())?;
        }
    }
    Ok(())
}

pub fn store(dst: Ssa, src: Ssa, pool: &mut RegPool, output: &mut impl Write) -> Result<(), Box<dyn Error>> {
    match (src.storage, dst.storage) {
        (Storage::BpOffset { off: src_off, pointer: src_pointer }, Storage::BpOffset { off: dst_off, pointer: _dst_pointer }) => {
            let tmp = pool.get_unused(Pointer::size(), Name::Name("tmp1".to_owned().into())).unwrap();
            // writeln!(output, "; {} <= {}+bp", tmp.name, src_off)?;
            writeln!(output, "    mov{} {} bp", Pointer::size(), tmp.storage.display())?;
            writeln!(output, "    sub{} {} ${}", Pointer::size(), tmp.storage.display(), -src_off)?;
            
            writeln!(output, "; {} <= addr of {}", dst.name, src.name)?;
            writeln!(output, "    mov{} [{}+bp] {}", src_pointer.pointee_size, dst_off, tmp.storage.display())?;
            pool.reinsert(tmp);
        }
        (Storage::BpOffset { off: src_off, pointer: src_pointer }, dst_storage) => {
            writeln!(output, "    mov{} [{}] [{}+bp]", src_pointer.pointee_size(), dst_storage.display(), src_off)?;
        }
        (src_storage, Storage::BpOffset { off: dst_off, pointer: dst_pointer }) => {
            let src_ptr = pool.push_stack(Name::Name(format!("{}_ptr", src.name).into()), Pointer::size());
            let tmp2 = pool.get_unused(Pointer::size(), Name::Name(format!("{}_ptr_tmp", src.name).into())).unwrap();
            // writeln!(output, "    mov{} {} [{}+bp]", Pointer::size(), tmp.storage.display(), dst_off)?;
            writeln!(output, "    mov{} {} {}", src_ptr.size, src_ptr.storage.display(), src_storage.display())?;
            if let Storage::BpOffset { off: src_off, pointer: _tmp_ptr } = src_ptr.storage {
                writeln!(output, "    mov{} {} bp", Pointer::size(), tmp2.storage.display())?;
                writeln!(output, "    sub{} {} ${}", Pointer::size(), tmp2.storage.display(), -src_off)?;
                
                writeln!(output, "; {} <= addr of {}", dst.name, src.name)?;
                writeln!(output, "    mov{} [{}+bp] {}", dst_pointer.pointee_size, dst_off, tmp2.storage.display())?;
            } else {
                unreachable!()
            }
            
            pool.reinsert(tmp2);
        }
        (src_storage, dst_storage) => {
            writeln!(output, "    mov{} [{}] {}", dst.size, dst_storage.display(), src_storage.display())?;
        }
    }
    Ok(())
}

impl Parser {
    pub fn new(bc_path: impl AsRef<Path>) -> Self {
        Self {
            module: Module::from_bc_path(bc_path).unwrap(),
            output: String::new(),
        }
    }

    pub fn emit_k4sm(&mut self) -> Result<String, Box<dyn Error>> {
        for func in self.module.functions.iter() {
            
            writeln!(self.output, "%{}", func.name)?;
            writeln!(self.output, "    push q bp")?;
            writeln!(self.output, "    mov q bp sp")?;
            
            let mut pool = RegPool::new(func.parameters.to_owned(), &mut self.output);
            let last_block = pool.get_unused(OpSize::Word, Name::Name("last_block".to_owned().into())).unwrap();
            writeln!(self.output, "    mov q {} %{}", last_block.storage.display(), func.name)?;
            for block in func.basic_blocks.iter() {
                let block_ssa = pool.label(func.name.clone(), block.name.to_string()[1..].to_owned());
                writeln!(
                    self.output,
                    "{}", block_ssa.storage.display()
                )?;
                
                // writeln!(self.output, "    pop q {}", last_block.storage.display())?;
                // pool.rel_sp += 8;
                // let mut last_dst = None;
                for instr in block.instrs.iter() {
                    println!();
                    println!("  {}", instr);
                    writeln!(self.output)?;
                    macro_rules! match_arith {
                        ($instr:expr, $mn:literal) => {{
                            let a =
                                parse_operand(&$instr.operand0, &mut pool, true);
                            let b =
                                parse_operand(&$instr.operand1, &mut pool, true);
                            assert_eq!(a.size, b.size);
                            let dst = pool.get_or_push_stack($instr.dest.to_owned(), a.size);

                            writeln!(
                                self.output,
                                "; {}",
                                $instr
                            )?;
                            writeln!(
                                self.output,
                                "    mov{} {} {}",
                                dst.size,
                                dst.storage.display(),
                                a.storage.display()
                            )?;
                            writeln!(
                                self.output,
                                concat!("    ", $mn, "{} {} {}"),
                                dst.size,
                                dst.storage.display(),
                                b.storage.display()
                            )?;
                            // pool.reinsert(a);
                            // pool.reinsert(b);
                        }};
                    }
                    match instr {
                        Instruction::Alloca(instr) => {
                            // this is a pointer
                            pool.push_stack(instr.dest.to_owned(), op_size(&instr.allocated_type));
                            // last_dst = Some(ssa.clone());
                        }
                        Instruction::Store(instr) => {
                            let dst =
                                parse_operand(&instr.address, &mut pool, false);
                            let src =
                                parse_operand(&instr.value, &mut pool, true);
                            writeln!(self.output, "; {}", instr)?;
                            store(dst, src, &mut pool, &mut self.output)?;
                            // pool.reinsert(tmp_dst);
                        }
                        Instruction::Load(instr) => {
                            let src =
                                parse_operand(&instr.address, &mut pool, true);
                            let dst =
                                pool.get_or_push_stack(instr.dest.to_owned(), src.size);
                                // let size = std::cmp::max(src.size, dst.size);
                            writeln!(self.output, "; {}", instr)?;
                            load(dst, src, OpSize::from_alignment(instr.alignment), &mut pool, &mut self.output)?;
                        }
                        Instruction::Add(instr) => match_arith!(instr, "add"),
                        Instruction::Sub(instr) => match_arith!(instr, "sub"),
                        Instruction::Mul(instr) => match_arith!(instr, "mul"),
                        Instruction::Shl(instr) => match_arith!(instr, "shl"),
                        Instruction::ICmp(instr) => {

                            let a = parse_operand(&instr.operand0, &mut pool, true);
                            let b = parse_operand(&instr.operand1, &mut pool, true);
                            let size = std::cmp::max(a.size, b.size);
                            let predicate = match instr.predicate {
                                IntPredicate::EQ => "jeq",
                                IntPredicate::ULT => "jlt",
                                IntPredicate::NE => "jne",
                                _ => todo!(),
                            };
                            // assert_eq!(a.storage.size(), b.storage.size());
                            let dest = pool.get_or_push_stack(instr.dest.to_owned(), OpSize::Byte);
                            let true_dest_name = format!("%__{}_{}_{}_{}_{}_true", func.name, instr.dest.clone(), a.name, b.name, predicate);
                            let false_dest_name = format!("%__{}_{}_{}_{}_{}_false", func.name, instr.dest.clone(), a.name, b.name, predicate);
                            let end_dest_name = format!("%__{}_{}_{}_{}_{}_end", func.name, instr.dest.clone(), a.name, b.name, predicate);
                            writeln!(self.output, "; {}", instr)?;
                            writeln!(self.output, "    cmp{} {} {}", size, a.storage.display(), b.storage.display())?;
                            writeln!(self.output, "    {} q {}", predicate, true_dest_name)?;
                            writeln!(self.output, "    jmp q {}", false_dest_name)?;
                            writeln!(self.output, "{}", true_dest_name)?;
                            writeln!(self.output, "    mov{} {} $1", dest.size, dest.storage.display())?;
                            writeln!(self.output, "    jmp q {}", end_dest_name)?;
                            writeln!(self.output, "{}", false_dest_name)?;
                            writeln!(self.output, "    mov{} {} $0", dest.size, dest.storage.display())?;
                            writeln!(self.output, "{}", end_dest_name)?;
                        }
                        Instruction::ZExt(instr) => {
                            let src = parse_operand(&instr.operand, &mut pool, true);
                            let to_type = op_size(&instr.to_type);
                            let dst = pool.get_or_push_stack(instr.dest.to_owned(), to_type);
                            
                            writeln!(self.output, "    mov{} {} {} ; {}", to_type, dst.storage.display(), src.storage.display(), instr)?;
                        }
                        Instruction::GetElementPtr(instr) => {
                            let src = parse_operand(&instr.address, &mut pool, true);
                            let size = if let Storage::BpOffset { off, pointer } = src.storage {
                                pointer.pointee_size
                            } else {
                                OpSize::Qword
                            };
                            // let size = OpSize::Byte;
                            // let tmp = pool.get_unused(src.size, Name::Name("tmp".to_owned().into())).unwrap();
                            let dst = pool.get_or_push_stack(instr.dest.to_owned(), src.size);
                            let indices: Vec<Ssa> = instr.indices.iter().map(|ind| parse_operand(ind, &mut pool, true)).collect();
                            assert_eq!(indices.len(), 1);
                            let index = &indices[0];
                            writeln!(self.output, "; {}", instr)?;
                            let tmp1 = pool.get_unused(src.size, Name::Name("tmp1".to_owned().into())).unwrap();
                            writeln!(self.output, "    mov{} {} {}", dst.size, tmp1.storage.display(), src.storage.display())?;
                            writeln!(self.output, "    add{} {} {}", dst.size, tmp1.storage.display(), index.storage.display())?;
                            writeln!(self.output, "    mov{} {} {}", size, dst.storage.display(), tmp1.storage.display())?;
                            pool.reinsert(tmp1);
                            // pool.reinsert(tmp);
                        }
                        Instruction::Phi(instr) => { // "which of these labels did we just come from?"
                            let dest = pool.get_or_push_stack(instr.dest.to_owned(), op_size(&instr.to_type));
                            let end = pool.label(func.name.clone(), format!("%__{}_phi_{}_end", func.name.clone(), last_block.name.clone()));
                            let mut yesses = vec![];
                            for (val, label) in instr.incoming_values.iter() {
                                let val = parse_operand(val, &mut pool, false);
                                let label = pool.label(func.name.clone(), label.to_string());
                                let yes = pool.label(func.name.clone(), format!("%__{}_phi_{}_{}", func.name.clone(), last_block.name.clone(), label.name.clone()));
                                yesses.push((yes.clone(), val.clone()));
                                writeln!(self.output, "    cmp q {} {}", last_block.storage.display(), label.storage.display())?;
                                writeln!(self.output, "    jeq q {}", yes.storage.display())?;
                            }
                            writeln!(self.output, "    hlt")?;
                            for (yes, val) in yesses.iter() {
                                writeln!(self.output, "{}", yes.storage.display())?;
                                writeln!(self.output, "    mov q {} {}", dest.storage.display(), val.storage.display())?;
                                writeln!(self.output, "    jmp q {}", end.storage.display())?;
                            }

                            writeln!(self.output, "{}", end.storage.display())?;
                        }
                        x => {
                            println!("WARNING: UNKNOWN INSTRUCTION:    {}", x)
                        }
                    }
                }
                // pool.rel_sp -= 8;
                writeln!(self.output, "    mov q {} {}", last_block.storage.display(), block_ssa.storage.display())?;
                match &block.term {
                    Terminator::Ret(Ret { return_operand, .. }) => {
                        let ret = parse_operand(return_operand.as_ref().unwrap(), &mut pool, true);
                        writeln!(self.output, "    mov{} ra {}", ret.size, ret.storage.display())?;
                        writeln!(self.output, "    pop q bp")?;
                        writeln!(self.output, "    ret")?;
                    }
                    Terminator::CondBr(CondBr { condition, true_dest, false_dest, .. }) => {
                        let cond = parse_operand(condition, &mut pool, true);
                        let true_dest = pool.label(func.name.clone(), true_dest.to_owned().to_string());
                        let false_dest = pool.label(func.name.clone(), false_dest.to_owned().to_string());
                        writeln!(self.output, "    cmp{} {} $0", cond.size, cond.storage.display())?;
                        writeln!(self.output, "    jeq q {}", false_dest.storage.display())?;
                        writeln!(self.output, "    jmp q {}", true_dest.storage.display())?;
                    }
                    Terminator::Br(Br { dest, ..}) => {
                        let dest = pool.label(func.name.clone(), dest.to_string());
                        writeln!(self.output, "    jmp q {}", dest.storage.display())?;
                    }
                    x => todo!("{}", x),
                };
                
                // last_ret = Some(ret.clone());
            }

            
        }

        Ok(self.output.clone())
    }
}

mod tests {
    #[test]
    fn test_emit_k4sm() {
        use super::Parser;
        let mut parser = Parser::new("/home/cls/code/k4s/teststuff/test.bc");
        parser.emit_k4sm().unwrap();
        println!("{}", parser.output.clone());
    }
}
