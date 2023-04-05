use std::{
    collections::{HashMap, HashSet, BTreeSet},
    fmt::Write,
};

use k4s::{Literal, InstructionSize};
use llvm_ir::{function::Parameter, Name};

use crate::{
    llvm::op_size,
    llvm::{Ssa, Storage},
};

use super::ssa::{CompositeType, CompositeTypeStorage, Register};

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
    pub used_regs: HashMap<String, Ssa>,
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
        for size in [InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword].iter() {
            let ssa = Ssa::new(Storage::Register { reg: Register::Rz }, *size, format!("rz{}", size.in_bytes()));
            this.insert(ssa);
        }
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
            writeln!(output, "; {} <= {}", stack_ptr.name, reg.display()).unwrap();
            writeln!(
                output,
                "    mov{} {} {}",
                stack_ptr.size,
                stack_ptr.storage.display(),
                reg.display()
            )
            .unwrap();
        }
        this
    }

    pub fn insert(&mut self, ssa: Ssa) {
        assert!(self.used_regs.insert(ssa.name.clone(), ssa).is_none());
    }

    pub fn take_back(&mut self, ssa: Ssa) {
        assert!(self.used_regs.remove(&ssa.name).is_some());
        if let Storage::Register { reg } = ssa.storage {
            assert!(self.avail_regs.insert(reg));
        } else {
            // pop stack?
            todo!()
        }
    }

    pub fn push_composite(&mut self, name: &str, storage: CompositeTypeStorage) -> Ssa {
        self.stack_size += storage.size_in_bytes();
        self.stack_size += 16 - self.stack_size % 16;

        let ssa = Ssa::new(Storage::Composite { stack_offset: self.stack_size, ident: name.to_owned(), is_packed: true, typ_storage: storage }, InstructionSize::Unsized, name.to_owned());
        self.used_regs.insert(ssa.name.to_owned(), ssa.clone());

        ssa
    }

    pub fn push_pointer(&mut self, name: &str, pointee: Box<Ssa>) -> Ssa {
        self.stack_size += InstructionSize::Qword.in_bytes();
        self.stack_size += 16 - self.stack_size % 16;

        let ssa = Ssa::new(
            Storage::Pointer {
                stack_offset: self.stack_size,
                pointee,
            },
            InstructionSize::Qword,
            name.to_owned(),
        );
        self.used_regs.insert(name.to_owned(), ssa.clone());

        ssa
    }

    pub fn get(&self, name: &str) -> Option<Ssa> {
        self.used_regs.get(name).cloned()
    }

    pub fn push_literal(&mut self, name: &str, value: Literal, signed: bool) -> Ssa {
        self.stack_size += value.size().in_bytes();
        self.stack_size += 16 - self.stack_size % 16;
        let ssa = Ssa::new(
            Storage::Literal { stack_offset: self.stack_size, value, signed },
            value.size(),
            name.to_owned(),
        );
        self.used_regs.insert(name.to_owned(), ssa.clone());
        ssa
    }

    pub fn rz(&self, size: InstructionSize) -> Ssa {
        let size = if matches!(size, InstructionSize::Unsized) { InstructionSize::Byte } else { size };
        self.get(&format!("rz{}", size.in_bytes())).unwrap()
    }

    pub fn label(&mut self, func_name: &str, name: &str) -> Ssa {
        let name = name.strip_prefix('%').unwrap_or(name);
        let name: Name = format!("{func_name}{name}").into();
        self.used_regs
            .get(&name.to_string())
            .cloned()
            .unwrap_or_else(|| {
                let ssa = Ssa::new(
                    Storage::Label {
                        label: name.clone().to_string(),
                    },
                    InstructionSize::Qword,
                    name.clone().to_string(),
                );
                self.used_regs.insert(name.clone().to_string(), ssa.clone());
                ssa
            })
    }

    #[must_use = "This returns None if there aren't any available registers!"]
    pub fn get_unused(&mut self, name: &str, size: InstructionSize) -> Option<Ssa> {
        for reg in GP_REGS.iter() {
            if self.avail_regs.remove(reg) {
                let ssa = Ssa::new(Storage::Register { reg: reg.clone() }, size, name.to_owned());
                self.used_regs.insert(name.to_owned(), ssa.clone());
                return Some(ssa);
            }
        }
        None
    }
}
