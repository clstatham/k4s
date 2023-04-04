use std::{collections::{HashMap, HashSet}, fmt::Write};

use k4s::{OpSize, Literal};
use llvm_ir::{function::Parameter, Name};

use crate::{llvm::{Ssa, Storage}, llvm::op_size};

const ALL_REGS: &[Storage] = &[Storage::Ra, Storage::Rb, Storage::Rc, Storage::Rd, Storage::Re, Storage::Rf, Storage::Rg, Storage::Rh, Storage::Ri, Storage::Rj, Storage::Rk, Storage::Rl];

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
            let stack_ptr = this.get_unused(op_size(&param.ty), param.name.to_owned()).unwrap();
            writeln!(output, "; {} <= {}", stack_ptr.name, reg.display()).unwrap();
            writeln!(
                output,
                "    mov{} {} {}",
                stack_ptr.size,
                stack_ptr.storage.display(),
                reg.display()
            )
            .unwrap();
            // this.avail_regs.remove(reg);
            // this.used_regs
            //     .insert(param.name.to_owned(), Ssa::new(reg.clone(), op_size(&param.ty), param.name.to_owned()));
        }
        this
    }

    pub fn insert(&mut self, ssa: Ssa) {
        assert!(!self.avail_regs.remove(&ssa.storage));
        assert!(self.used_regs.insert(ssa.name.clone(), ssa).is_none());
    }

    pub fn reinsert(&mut self, ssa: Ssa) {
        assert!(self.used_regs.remove(&ssa.name).is_some());
        assert!(self.avail_regs.insert(ssa.storage));
    }

    pub fn push_stack(&mut self, name: String, size: OpSize) -> Ssa {
        self.rel_sp -= OpSize::Qword.in_bytes() as isize;
        self.rel_sp -= self.rel_sp % OpSize::Qword.in_bytes() as isize; // align down
        
        let ssa = Ssa::new(
            Storage::StackLocal {
                off: self.rel_sp,
                pointed_size: size,
            },
            OpSize::Qword,
            name.clone(),
        );
        self.used_regs.insert(name, ssa.clone());
        self.avail_regs.remove(&ssa.storage);

        ssa
    }

    pub fn get(&self, name: String) -> Option<Ssa> {
        self.used_regs.get(&name).cloned()
    }

    pub fn constant(&mut self, name: String, value: Literal, signed: bool) -> Ssa {
        let ssa = Ssa::new(
            Storage::Constant { value, signed },
            value.size(),
            name.clone(),
        );
        self.used_regs.insert(name, ssa.clone());
        self.avail_regs.remove(&ssa.storage);
        ssa
    }

    pub fn label(&mut self, func_name: String, name: String) -> Ssa {
        let name = name.strip_prefix('%').unwrap_or(&name);
        let name = format!("{func_name}{name}");
        let name = Name::Name(name.into());
        self.used_regs
            .get(&name.to_string())
            .cloned()
            .unwrap_or_else(|| {
                let ssa = Ssa::new(
                    Storage::Label {
                        label: name.clone().to_string(),
                    },
                    OpSize::Qword,
                    name.clone().to_string(),
                );
                self.used_regs.insert(name.clone().to_string(), ssa.clone());
                self.avail_regs.remove(&ssa.storage);
                ssa
            })
    }

    #[must_use = "This returns None if there aren't any available registers!"]
    pub fn get_unused(&mut self, size: OpSize, name: Name) -> Option<Ssa> {
        for reg in ALL_REGS.iter() {
            if self.avail_regs.remove(reg) {
                let ssa = Ssa::new(reg.clone(), size, name.to_string());
                self.used_regs.insert(name.to_string(), ssa.clone());
                return Some(ssa);
            }
        }
        None
    }
}