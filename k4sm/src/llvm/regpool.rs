use std::{
    collections::{HashMap, HashSet},
    fmt::Write, rc::Rc,
};

use k4s::{InstructionSize, Literal};
use llvm_ir::{function::Parameter, Name};

use crate::{llvm::op_size, llvm::Ssa};

use super::ssa::Register;

const GP_REGS: &[Register] = &[
    Register::Ra,
    Register::Rb,
    Register::Rc,
    Register::Rd,
    Register::Re,
    Register::Rf,
    Register::Rg,
    Register::Rh,
    Register::Ri,
    Register::Rj,
    Register::Rk,
    Register::Rl,
];

#[derive(Default)]
pub struct RegPool {
    pub used_regs: HashMap<String, Rc<Ssa>>,
    pub avail_regs: HashSet<Register>,
    pub stack_size: usize,
}
impl RegPool {
    pub fn new(params: Vec<Parameter>, output: &mut impl Write) -> Self {
        let mut this = Self {
            stack_size: 0,
            used_regs: HashMap::new(),
            avail_regs: GP_REGS.iter().cloned().collect(),
        };
        for (param, reg) in params.iter().zip(
            [
                Register::Rg,
                Register::Rh,
                Register::Ri,
                Register::Rj,
                Register::Rk,
                Register::Rl,
            ][..params.len()]
                .iter(),
        ) {
            let stack_ptr = this
                .get_unused(&param.name.to_string(), op_size(&param.ty))
                .unwrap();
            println!(
                "; {} {} <= {}",
                stack_ptr.size(),
                stack_ptr.name(),
                reg.display()
            );
            writeln!(output, "; {} <= {}", stack_ptr.display(), reg.display()).unwrap();
            writeln!(
                output,
                "    mov{} {} {}",
                stack_ptr.size(),
                stack_ptr.display(),
                reg.display()
            )
            .unwrap();
        }
        this
    }

    pub fn insert(&mut self, ssa: Rc<Ssa>) {
        assert!(self.used_regs.insert(ssa.name(), ssa.clone()).is_none(), "Tried to insert {} but it already exists", ssa.name());
    }

    pub fn take_back(&mut self, name: &str, ssa: Rc<Ssa>) {
        assert!(self.used_regs.remove(name).is_some());
        if let Ssa::Register {
            name: _,
            reg,
            size: _,
        } = ssa.as_ref()
        {
            assert!(self.avail_regs.insert(reg.clone()));
        } else {
            // pop stack?
            todo!()
        }
    }

    pub fn push(&mut self, mut ssa: Ssa) -> Rc<Ssa> {
        self.stack_size += ssa.size_in_bytes();
        self.stack_size += 16 - self.stack_size % 16;

        match &mut ssa {
            Ssa::Literal { stack_offset, .. } => *stack_offset = self.stack_size,
            Ssa::Pointer { stack_offset, .. } => *stack_offset = self.stack_size,
            Ssa::Array { stack_offset, .. } => *stack_offset = self.stack_size,
            Ssa::Composite { stack_offset, .. } => *stack_offset = self.stack_size,
            t => unimplemented!("{:?}", t),
        }

        let ssa = Rc::new(ssa);
        self.used_regs.insert(ssa.name(), ssa.clone());

        ssa
    }

    pub fn push_pointer(&mut self, name: &str, pointee: Rc<Ssa>) -> Rc<Ssa> {
        self.stack_size += InstructionSize::Qword.in_bytes();
        self.stack_size += 16 - self.stack_size % 16;

        let ssa = Ssa::Pointer {
            name: name.to_owned(),
            stack_offset: self.stack_size,
            pointee,
        };
        let ssa = Rc::new(ssa);
        self.used_regs.insert(name.to_owned(), ssa.clone());

        ssa
    }

    pub fn get(&self, name: &str) -> Option<Rc<Ssa>> {
        self.used_regs.get(name).cloned()
    }

    pub fn push_literal(&mut self, name: &str, value: Literal, signed: bool) -> Rc<Ssa> {
        self.stack_size += value.size().in_bytes();
        self.stack_size += 16 - self.stack_size % 16;
        let ssa = Ssa::Literal {
            name: name.to_owned(),
            stack_offset: self.stack_size,
            value,
            signed,
        };
        let ssa = Rc::new(ssa);
        self.used_regs.insert(name.to_owned(), ssa.clone());
        ssa
    }

    pub fn label(&mut self, func_name: &str, name: &str) -> Rc<Ssa> {
        let name = name.strip_prefix('%').unwrap_or(name);
        let name: Name = format!("{func_name}{name}").into();
        self.used_regs
            .get(&name.to_string())
            .cloned()
            .unwrap_or_else(|| {
                let ssa = Ssa::Label {
                    label: name.clone().to_string(),
                };
                let ssa = Rc::new(ssa);
                self.used_regs.insert(name.clone().to_string(), ssa.clone());
                ssa
            })
    }

    #[must_use = "This returns None if there aren't any available registers!"]
    pub fn get_unused(&mut self, name: &str, size: InstructionSize) -> Option<Rc<Ssa>> {
        for reg in GP_REGS.iter() {
            if self.avail_regs.remove(reg) {
                let ssa = Ssa::Register {
                    name: name.to_owned(),
                    reg: reg.clone(),
                    size,
                };
                let ssa = Rc::new(ssa);
                self.used_regs.insert(name.to_owned(), ssa.clone());
                return Some(ssa);
            }
        }
        None
    }
}
