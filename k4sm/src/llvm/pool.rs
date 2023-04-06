use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    rc::Rc,
};

use k4s::{InstructionSize, Literal};
use llvm_ir::{function::Parameter, Name, types::Types};

use crate::{llvm::op_size, llvm::Ssa};

use super::ssa::Register;

pub const GP_REGS: &[Register] = &[
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
pub struct Pool {
    pub used: HashMap<String, Rc<Ssa>>,
    pub avail_regs: HashSet<Register>,
    clobbered_regs: HashSet<Register>,
    pub stack_size: usize,
}
impl Pool {
    pub fn new(params: Vec<Parameter>, types: &Types, output: &mut impl Write) -> Self {
        let mut this = Self {
            stack_size: 0,
            used: HashMap::new(),
            clobbered_regs: HashSet::new(),
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
            // let stack_ptr = this
            //     .push_primitive(&param.name.to_string(), Literal::default_for_size(op_size(&param.ty)), false);
            let stack_ptr = Ssa::push(&param.ty, param.name.to_string(), types, &mut this);
            println!(
                "; {} {} <= {}",
                stack_ptr.size(),
                stack_ptr.name(),
                reg
            );
            writeln!(output, "; {} <= {}", stack_ptr, reg).unwrap();
            writeln!(
                output,
                "    mov{} {} {}",
                stack_ptr.size(),
                stack_ptr,
                reg
            )
            .unwrap();
        }
        this
    }

    pub fn insert(&mut self, ssa: Rc<Ssa>) {
        assert!(
            self.used.insert(ssa.name(), ssa.clone()).is_none(),
            "Tried to insert {} but it already exists",
            ssa.name()
        );
    }

    pub fn take_back(&mut self, name: &str, ssa: Rc<Ssa>) {
        assert!(self.used.remove(name).is_some());
        if let Ssa::Register {
            name: _,
            reg,
            size: _,
        } = ssa.as_ref()
        {
            assert!(self.avail_regs.insert(*reg));
        } else {
            // pop stack?
            todo!()
        }
    }

    fn align_stack(&mut self) {
        self.stack_size += 8 - self.stack_size % 8;
    }

    pub fn push(&mut self, mut ssa: Ssa) -> Rc<Ssa> {
        self.stack_size += ssa.size_in_bytes();
        self.align_stack();

        match &mut ssa {
            Ssa::Primitive { stack_offset, .. } => *stack_offset = self.stack_size,
            Ssa::Pointer { stack_offset, .. } => *stack_offset = self.stack_size,
            Ssa::Composite { stack_offset, .. } => *stack_offset = self.stack_size,
            Ssa::StaticComposite { name, is_packed, elements } => {
                ssa = Ssa::Composite { name: name.clone(), stack_offset: self.stack_size, is_packed: *is_packed , elements: elements.clone() };
            }
            Ssa::StaticPointer { name, pointee } => {
                ssa = Ssa::Pointer { name: name.clone(), stack_offset: self.stack_size, pointee: pointee.clone() };
            }
            Ssa::Constant { name, value, signed } => {
                ssa = Ssa::Primitive { name: name.clone(), stack_offset: self.stack_size, size: value.size(), signed: *signed };
            }
            t => unimplemented!("{:?}", t),
        }

        let ssa = Rc::new(ssa);
        self.used.insert(ssa.name(), ssa.clone());

        ssa
    }

    pub fn push_pointer(&mut self, name: &str, pointee: Option<Rc<Ssa>>) -> Rc<Ssa> {
        self.stack_size += InstructionSize::Qword.in_bytes();
        self.align_stack();

        let ssa = Ssa::Pointer {
            name: name.to_owned(),
            stack_offset: self.stack_size,
            pointee,
        };
        let ssa = Rc::new(ssa);
        self.used.insert(name.to_owned(), ssa.clone());

        ssa
    }

    pub fn get(&self, name: &str) -> Option<&Rc<Ssa>> {
        self.used.get(name)
    }

    pub fn take(&mut self, name: &str) -> Option<Rc<Ssa>> {
        self.used.remove(name)
    }

    pub fn push_primitive(&mut self, name: &str, size: InstructionSize, signed: bool) -> Rc<Ssa> {
        self.stack_size += size.in_bytes();
        self.align_stack();
        let ssa = Ssa::Primitive {
            name: name.to_owned(),
            stack_offset: self.stack_size,
            size,
            signed,
        };
        let ssa = Rc::new(ssa);
        self.used.insert(name.to_owned(), ssa.clone());
        ssa
    }

    pub fn label(&mut self, func_name: &str, name: &str) -> Rc<Ssa> {
        let name = name.strip_prefix('%').unwrap_or(name);
        let name: Name = format!("{func_name}{name}").into();
        self.used
            .get(&name.to_string())
            .cloned()
            .unwrap_or_else(|| {
                let ssa = Ssa::Label {
                    name: name.clone().to_string(),
                };
                let ssa = Rc::new(ssa);
                self.used.insert(name.clone().to_string(), ssa.clone());
                ssa
            })
    }

    #[must_use = "This returns None if there aren't any available registers!"]
    pub fn get_unused_register(&mut self, name: &str, size: InstructionSize) -> Option<Rc<Ssa>> {
        for reg in GP_REGS.iter() {
            if self.avail_regs.remove(reg) {
                let ssa = Ssa::Register {
                    name: name.to_owned(),
                    reg: *reg,
                    size,
                };
                self.clobbered_regs.insert(*reg);
                let ssa = Rc::new(ssa);
                self.used.insert(name.to_owned(), ssa.clone());
                return Some(ssa);
            }
        }
        None
    }

    pub fn clobbered_regs(&self) -> &HashSet<Register> {
        &self.clobbered_regs
    }
}
