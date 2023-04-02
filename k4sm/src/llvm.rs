// #![allow(unused_variables)]

use std::{path::Path, error::Error, collections::{HashMap, HashSet}, fmt::Write};

use llvm_ir::{Module, Instruction, Operand, Type, instruction::{Alloca, Load}, function::Parameter, Name, Terminator, terminator::Ret};

pub struct Parser {
    module: Module,
    output: String,
}

#[derive(Clone)]
pub enum SsaType {
    Param(Parameter),
    Alloca(Alloca),
    Load(Load),
}

impl SsaType {
    pub fn name(&self) -> Name {
        match self {
            Self::Param(x) => x.name.to_owned(),
            Self::Alloca(x) => x.dest.to_owned(),
            Self::Load(x) => x.dest.to_owned(),
        }
    }
}

#[derive(Clone)]
pub struct Ssa {
    pub name: Name,
    pub reg: GpReg,
}

impl Ssa {
    pub fn new(reg: GpReg, name: Name) -> Self {
        Self { name, reg }
    }
}

const ALL_REGS: &[GpReg] = &[GpReg::Ra, GpReg::Rb, GpReg::Rc, GpReg::Rd, GpReg::Re, GpReg::Rf, GpReg::Rg, GpReg::Rh, GpReg::Ri, GpReg::Rj, GpReg::Rk, GpReg::Rl];

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
pub enum GpReg {
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
    StackOffset { sp_at_creation: isize },
}

impl GpReg {
    fn display(&self, current_sp: isize) -> String {
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
            Self::StackOffset { sp_at_creation } => {
                let off = sp_at_creation - current_sp;
                return format!("[{off}+sp]")
            }
        };
        s.to_owned()
    }
}

pub struct RegPool {
    pub used_regs: HashMap<Name, Ssa>,
    pub avail_regs: HashSet<GpReg>,
    pub rel_sp: isize,
}
impl RegPool  {
    pub fn new(params: Vec<Parameter>) -> Self {
        let mut this = Self { rel_sp: 0, used_regs: HashMap::new(), avail_regs: ALL_REGS.iter().cloned().collect() };
        for (param, reg) in params.iter().zip([GpReg::Rg, GpReg::Rh, GpReg::Ri, GpReg::Rj, GpReg::Rk, GpReg::Rl][..params.len()].iter()) {
            // writeln!("; {reg} <= {}", param.name);
            this.avail_regs.remove(reg);
            this.used_regs.insert(param.name.to_owned(), Ssa::new(*reg, param.name.to_owned()));
        }
        this
    }

    pub fn reinsert(&mut self, ssa: Ssa) {
        assert!(self.used_regs.remove(&ssa.name).is_some());
        assert!(self.avail_regs.insert(ssa.reg));
    }

    pub fn push_stack(&mut self, name: Name, output: &mut impl Write) -> Ssa  {
        writeln!(output, "    sub sp $8").unwrap();
        self.rel_sp -= 8;
        let ssa = Ssa::new(GpReg::StackOffset { sp_at_creation: self.rel_sp }, name.clone());
        self.used_regs.insert(name, ssa.clone());
        
        ssa
    }

    pub fn get(&self, name: Name) -> Option<Ssa> {
        self.used_regs.get(&name).cloned()
    }    

    pub fn get_or_push_stack(&mut self, name: Name, output: &mut impl Write) -> Ssa {
        self.get(name.clone()).unwrap_or_else(|| self.push_stack(name, output))
    }

    #[must_use = "This returns None if there aren't any available registers!"]
    pub fn get_unused(&mut self, name: Name) -> Option<Ssa> {
        for reg in ALL_REGS.iter() {
            if self.avail_regs.remove(reg) {
                let ssa = Ssa::new(*reg, name.clone());
                self.used_regs.insert(name, ssa.clone());
                return Some(ssa)
            }
        }
        None
    }

    pub fn pick_for_me(&mut self, name: Name, output: &mut impl Write) -> Ssa {
        self.get(name.clone()).or_else(|| self.get_unused(name.clone())).unwrap_or_else(|| self.push_stack(name, output))
    }
}

impl Parser {
    pub fn new(bc_path: impl AsRef<Path>) -> Self {
        Self { module: Module::from_bc_path(bc_path).unwrap(), output: String::new() }
    }

    pub fn emit_k4sm(&mut self) -> Result<String, Box<dyn Error>> {
        for func in self.module.functions.iter() {
            let mut pool = RegPool::new(func.parameters.to_owned());
            writeln!(self.output, "%{}", func.name)?;
            writeln!(self.output, "    mov bp sp")?;
            let mut last_ret = None;
            for block in func.basic_blocks.iter() {
                writeln!(self.output, "%{}_{} ", func.name, &block.name.to_string()[1..])?;
                let ret = match &block.term {
                    Terminator::Ret(Ret { return_operand, .. }) => match return_operand.as_ref().unwrap() {
                        Operand::LocalOperand { name, .. } => name.to_owned(),
                        x => todo!("{}", x),
                    }
                    x => todo!("{}", x),
                };
                let ret = pool.pick_for_me(ret.clone(), &mut self.output);
                last_ret = Some(ret.clone());
                let mut last_dst = None;
                for instr in block.instrs.iter() {
                    // writeln!();
                    // writeln!("  {}", instr);
                    match instr {
                        Instruction::Alloca(instr) => {
                            let ssa = pool.pick_for_me(instr.dest.to_owned(), &mut self.output);
                            last_dst = Some(ssa.clone());
                            // writeln!("    {} = alloca", ssa.reg.display(pool.rel_sp));
                        }
                        Instruction::Store(instr) => {
                            let (dst, _dst_ty) = match &instr.address {
                                Operand::LocalOperand { name, ty } => (name.to_owned(), &**ty),
                                _ => todo!(),
                            };
                            let (src, _src_ty) = match &instr.value {
                                Operand::LocalOperand { name, ty } => (name.to_owned(), &**ty),
                                x => todo!("{}", x),
                            };
                            let dst = pool.get(dst).unwrap();
                            let src = pool.get(src).unwrap();
                            let tmp = pool.get_unused(Name::Name("tmp".to_owned().into())).unwrap();
                            writeln!(self.output, "    mov {} {}", tmp.reg.display(pool.rel_sp), dst.reg.display(pool.rel_sp))?;
                            writeln!(self.output, "    mov [{}] {}", tmp.reg.display(pool.rel_sp), src.reg.display(pool.rel_sp))?;
                            pool.reinsert(tmp);
                            last_dst = Some(dst.clone());
                            
                        }
                        Instruction::Load(instr) => {
                            let (src, _src_ty) = match &instr.address {
                                Operand::LocalOperand { name, ty } => (name.to_owned(), &**ty),
                                x => todo!("{}", x),
                            };
                            let dst = pool.get_or_push_stack(instr.dest.to_owned(), &mut self.output);
                            let src = pool.get(src).unwrap();
                            let tmp = pool.get_unused(Name::Name("tmp".to_owned().into())).unwrap();
                            writeln!(self.output, "    mov {} {}", tmp.reg.display(pool.rel_sp), src.reg.display(pool.rel_sp))?;
                            writeln!(self.output, "    mov {} [{}]", dst.reg.display(pool.rel_sp), tmp.reg.display(pool.rel_sp))?;
                            pool.reinsert(tmp);
                            last_dst = Some(dst.clone());
                            // writeln!("    {}", instr);
                        }
                        Instruction::Add(instr) => {
                            let (a, a_ty) = match &instr.operand0 {
                                Operand::ConstantOperand(con) => {
                                    let con = &**con;
                                    todo!("{}", con)
                                },
                                Operand::LocalOperand { name, ty } => (name.to_owned(), &**ty),
                                x => todo!("{}", x),
                            };
                            let (b, b_ty) = match &instr.operand1 {
                                Operand::ConstantOperand(con) => {
                                    let con = &**con;
                                    todo!("{}", con)
                                },
                                Operand::LocalOperand { name, ty } => (name.to_owned(), &**ty),
                                x => todo!("{}", x),
                            };
                            let dst = instr.dest.to_owned();
                            let dst = pool.get_or_push_stack(dst, &mut self.output);
                            let a = pool.get(a).unwrap();
                            let b = pool.get(b).unwrap();
                            last_dst = Some(dst.clone());
                            match (a_ty, b_ty) {
                                (Type::IntegerType { .. }, Type::IntegerType { .. }) => {
                                    writeln!(self.output, "    mov {} {}", dst.reg.display(pool.rel_sp), a.reg.display(pool.rel_sp))?;
                                    writeln!(self.output, "    add {} {}", dst.reg.display(pool.rel_sp), b.reg.display(pool.rel_sp))?;
                                }
                                x => todo!("{:?}", x),
                            }
                            // writeln!("    {}", instr);
                        }
                        x => {writeln!(self.output, "    {}", x)?},
                    }
                }
                if last_dst.as_ref().unwrap().reg != ret.reg {
                    writeln!(self.output, "    mov {} {}", ret.reg.display(pool.rel_sp), last_dst.unwrap().reg.display(pool.rel_sp))?;
                }
            }
            
            writeln!(self.output, "%{}_ret", func.name)?;
            if last_ret.as_ref().unwrap().reg != GpReg::Ra {
                writeln!(self.output, "    mov ra {}", last_ret.as_ref().unwrap().reg.display(pool.rel_sp))?;
            }
            writeln!(self.output, "    mov sp bp")?;
            writeln!(self.output, "    ret")?;
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