use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
};

use k4s::{Literal, InstructionSize};
use llvm_ir::{function::Parameter, Name};

use crate::{
    llvm::op_size,
    llvm::{Ssa, Storage},
};

const GP_REGS: &[Storage] = &[
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

#[derive(Default)]
pub struct RegPool {
    pub used_regs: HashMap<String, Ssa>,
    pub avail_regs: HashSet<Storage>,
    pub rel_sp: isize,
}
impl RegPool {
    pub fn new(params: Vec<Parameter>, output: &mut impl Write) -> Self {
        let mut this = Self {
            rel_sp: 0,
            used_regs: HashMap::new(),
            avail_regs: GP_REGS.iter().cloned().collect(),
        };
        for size in [InstructionSize::Byte, InstructionSize::Word, InstructionSize::Dword, InstructionSize::Qword].iter() {
            let ssa = Ssa::new(Storage::Rz, *size, format!("rz{}", size.in_bytes()));
            this.insert(ssa);
        }
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
        assert!(!self.avail_regs.remove(&ssa.storage));
        assert!(self.used_regs.insert(ssa.name.clone(), ssa).is_none());
    }

    pub fn take_back(&mut self, ssa: Ssa) {
        assert!(self.used_regs.remove(&ssa.name).is_some());
        assert!(self.avail_regs.insert(ssa.storage));
    }

    pub fn push_stack(&mut self, name: &str, size: InstructionSize, count: usize) -> Ssa {
        self.rel_sp -= count as isize * size.in_bytes() as isize;
        self.rel_sp -= self.rel_sp % InstructionSize::Qword.in_bytes() as isize; // align down

        let ssa = Ssa::new(
            Storage::StackLocal {
                off: self.rel_sp,
                pointed_size: size,
                count,
            },
            InstructionSize::Qword,
            name.to_owned(),
        );
        self.used_regs.insert(name.to_owned(), ssa.clone());
        self.avail_regs.remove(&ssa.storage);

        ssa
    }

    pub fn get(&self, name: &str) -> Option<Ssa> {
        self.used_regs.get(name).cloned()
    }

    pub fn constant(&mut self, name: &str, value: Literal, signed: bool) -> Ssa {
        let ssa = Ssa::new(
            Storage::Constant { value, signed },
            value.size(),
            name.to_owned(),
        );
        self.used_regs.insert(name.to_owned(), ssa.clone());
        self.avail_regs.remove(&ssa.storage);
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
                self.avail_regs.remove(&ssa.storage);
                ssa
            })
    }

    #[must_use = "This returns None if there aren't any available registers!"]
    pub fn get_unused(&mut self, name: &str, size: InstructionSize) -> Option<Ssa> {
        for reg in GP_REGS.iter() {
            if self.avail_regs.remove(reg) {
                let ssa = Ssa::new(reg.clone(), size, name.to_owned());
                self.used_regs.insert(name.to_owned(), ssa.clone());
                return Some(ssa);
            }
        }
        None
    }
}
