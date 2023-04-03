// #![allow(unused_variables)]

use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fmt::Write,
    path::Path,
    sync::atomic::AtomicUsize,
};

use k4s::{Literal, OpSize};
use llvm_ir::{
    function::Parameter,
    terminator::{Br, CondBr, Ret},
    Constant, Instruction, IntPredicate, Module, Name, Operand, Terminator, Type,
};

pub struct Parser {
    module: Module,
    output: String,
    pool: Option<RegPool>,
    function_name: String,
    last_block: Option<Ssa>,
}

#[derive(Clone)]
pub struct Ssa {
    pub name: String,
    pub storage: Storage,
    pub size: OpSize,
}

impl Ssa {
    pub fn new(storage: Storage, size: OpSize, name: String) -> Self {
        Self {
            name,
            storage,
            size,
        }
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
    Data { label: String, data: Vec<u8> },
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
            Self::Data { label, data: _ } => return label.to_owned(),
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

pub struct FunctionPool {
    pub known_functions: HashMap<Name, Ssa>,
}

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
            let stack_ptr = this.push_stack(param.name.to_owned().to_string(), op_size(&param.ty));
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
        self.rel_sp -= Pointer::size().in_bytes() as isize;
        self.rel_sp -= self.rel_sp % Pointer::size().in_bytes() as isize; // align down
        let ssa = Ssa::new(
            Storage::BpOffset {
                off: self.rel_sp,
                pointer: Pointer { pointee_size: size },
            },
            Pointer::size(),
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
                        name: name.clone().to_string(),
                    },
                    OpSize::Qword,
                    name.clone().to_string(),
                );
                self.used_regs.insert(name.clone().to_string(), ssa.clone());
                self.avail_regs.remove(&ssa.storage);
                ssa
            })
    }

    pub fn get_or_push_stack(&mut self, name: Name, size: OpSize) -> Ssa {
        // self.get(name.clone())
        //     .unwrap_or_else(|| self.push_stack(name, output))
        if let Some(ssa) = self.get(name.to_string()) {
            ssa
        } else {
            self.push_stack(name.to_string(), size)
        }
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

    pub fn pick_for_me(&mut self, name: Name, size: OpSize) -> Ssa {
        self.get(name.to_string())
            .or_else(|| self.get_unused(size, name.clone()))
            .or_else(|| Some(self.push_stack(name.to_string(), size)))
            .unwrap()
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
        Type::PointerType { .. } => Pointer::size(),
        _ => todo!(),
    }
}

// static DATA_LABELS: AtomicUsize = AtomicUsize::new(0);

impl Parser {
    pub fn new(bc_path: impl AsRef<Path>) -> Self {
        Self {
            module: Module::from_bc_path(bc_path).unwrap(),
            output: String::new(),
            function_name: String::new(),
            last_block: None,
            pool: None,
        }
    }

    pub fn function_name(&self) -> String {
        self.function_name.clone()
    }

    pub fn pool(&mut self) -> &mut RegPool {
        self.pool.as_mut().unwrap()
    }

    fn parse_instr(&mut self, instr: &Instruction) -> Result<(), Box<dyn Error>> {
        macro_rules! match_arith {
            ($instr:expr, $mn:literal) => {{
                let a = self.parse_operand(None, &$instr.operand0, true)?;
                let b = self.parse_operand(None, &$instr.operand1, true)?;
                assert_eq!(a.size, b.size);
                let dst = self
                    .pool()
                    .get_or_push_stack($instr.dest.to_owned(), a.size);

                writeln!(&mut self.output, "; {}", $instr)?;
                writeln!(
                    &mut self.output,
                    "    mov{} {} {}",
                    dst.size,
                    dst.storage.display(),
                    a.storage.display()
                )?;
                writeln!(
                    &mut self.output,
                    concat!("    ", $mn, "{} {} {}"),
                    dst.size,
                    dst.storage.display(),
                    b.storage.display()
                )?;
                // pool.reinsert(a);
                // pool.reinsert(b);
            }};
        }
        let function_name = self.function_name();
        let last_block = self.last_block.as_ref().unwrap().clone();
        match instr {
            Instruction::Alloca(instr) => {
                // this is a pointer
                self.pool().push_stack(
                    instr.dest.to_owned().to_string(),
                    op_size(&instr.allocated_type),
                );
                // last_dst = Some(ssa.clone());
            }
            Instruction::Store(instr) => {
                let dst = self.parse_operand(None, &instr.address, false)?;
                let src = self.parse_operand(None, &instr.value, true)?;
                writeln!(self.output, "; {}", instr)?;
                match (src.storage, dst.storage) {
                    (
                        Storage::BpOffset {
                            off: src_off,
                            pointer: src_pointer,
                        },
                        Storage::BpOffset {
                            off: dst_off,
                            pointer: _dst_pointer,
                        },
                    ) => {
                        let tmp = self
                            .pool()
                            .get_unused(Pointer::size(), Name::Name("tmp1".to_owned().into()))
                            .unwrap();
                        // writeln!(output, "; {} <= {}+bp", tmp.name, src_off)?;
                        writeln!(
                            self.output,
                            "    mov{} {} bp",
                            Pointer::size(),
                            tmp.storage.display()
                        )?;
                        writeln!(
                            self.output,
                            "    sub{} {} ${}",
                            Pointer::size(),
                            tmp.storage.display(),
                            -src_off
                        )?;

                        writeln!(self.output, "; {} <= addr of {}", dst.name, src.name)?;
                        writeln!(
                            self.output,
                            "    mov{} [{}+bp] {}",
                            src_pointer.pointee_size,
                            dst_off,
                            tmp.storage.display()
                        )?;
                        self.pool().reinsert(tmp);
                    }
                    (
                        Storage::BpOffset {
                            off: src_off,
                            pointer: src_pointer,
                        },
                        dst_storage,
                    ) => {
                        writeln!(
                            self.output,
                            "    mov{} [{}] [{}+bp]",
                            src_pointer.pointee_size(),
                            dst_storage.display(),
                            src_off
                        )?;
                    }
                    (
                        src_storage,
                        Storage::BpOffset {
                            off: dst_off,
                            pointer: dst_pointer,
                        },
                    ) => {
                        let src_ptr = self
                            .pool()
                            .push_stack(format!("{}_ptr", src.name), Pointer::size());
                        let tmp2 = self
                            .pool()
                            .get_unused(
                                Pointer::size(),
                                Name::Name(format!("{}_ptr_tmp", src.name).into()),
                            )
                            .unwrap();
                        // writeln!(self.output, "    mov{} {} [{}+bp]", Pointer::size(), tmp.storage.display(), dst_off)?;
                        writeln!(
                            self.output,
                            "    mov{} {} {}",
                            src_ptr.size,
                            src_ptr.storage.display(),
                            src_storage.display()
                        )?;
                        if let Storage::BpOffset {
                            off: src_off,
                            pointer: _tmp_ptr,
                        } = src_ptr.storage
                        {
                            writeln!(
                                self.output,
                                "    mov{} {} bp",
                                Pointer::size(),
                                tmp2.storage.display()
                            )?;
                            writeln!(
                                self.output,
                                "    sub{} {} ${}",
                                Pointer::size(),
                                tmp2.storage.display(),
                                -src_off
                            )?;

                            writeln!(self.output, "; {} <= addr of {}", dst.name, src.name)?;
                            writeln!(
                                self.output,
                                "    mov{} [{}+bp] {}",
                                dst_pointer.pointee_size,
                                dst_off,
                                tmp2.storage.display()
                            )?;
                        } else {
                            unreachable!()
                        }

                        self.pool().reinsert(tmp2);
                    }
                    (src_storage, dst_storage) => {
                        writeln!(
                            self.output,
                            "    mov{} [{}] {}",
                            dst.size,
                            dst_storage.display(),
                            src_storage.display()
                        )?;
                    }
                }
                // pool.reinsert(tmp_dst);
            }
            Instruction::Load(instr) => {
                let src = self.parse_operand(None, &instr.address, true)?;
                let dst = self
                    .pool()
                    .get_or_push_stack(instr.dest.to_owned(), src.size);
                // let size = std::cmp::max(src.size, dst.size);
                writeln!(self.output, "; {}", instr)?;
                let align = OpSize::from_alignment(instr.alignment);
                match (src.storage, dst.storage) {
                    (
                        Storage::BpOffset {
                            off: src_off,
                            pointer: _src_pointer,
                        },
                        Storage::BpOffset {
                            off: dst_off,
                            pointer: _dst_pointer,
                        },
                    ) => {
                        let tmp = self
                            .pool()
                            .get_unused(Pointer::size(), Name::Name("tmp1".to_owned().into()))
                            .unwrap();
                        writeln!(
                            self.output,
                            "    mov{} {} [{}+bp]",
                            Pointer::size(),
                            tmp.storage.display(),
                            src_off
                        )?;
                        writeln!(
                            self.output,
                            "    mov{} [{}+bp] [{}]",
                            align,
                            dst_off,
                            tmp.storage.display()
                        )?;
                        self.pool().reinsert(tmp);
                    }
                    (
                        Storage::BpOffset {
                            off: src_off,
                            pointer: _src_pointer,
                        },
                        dst_storage,
                    ) => {
                        let tmp = self
                            .pool()
                            .get_unused(Pointer::size(), Name::Name("tmp".to_owned().into()))
                            .unwrap();
                        writeln!(
                            self.output,
                            "    mov{} {} [{}+bp]",
                            Pointer::size(),
                            tmp.storage.display(),
                            src_off
                        )?;
                        writeln!(
                            self.output,
                            "    mov{} {} [{}]",
                            align,
                            dst_storage.display(),
                            tmp.storage.display()
                        )?;
                        self.pool().reinsert(tmp);
                    }
                    (
                        src_storage,
                        Storage::BpOffset {
                            off: dst_off,
                            pointer: _dst_pointer,
                        },
                    ) => {
                        writeln!(
                            self.output,
                            "    mov{} [{}+bp] [{}]",
                            align,
                            dst_off,
                            src_storage.display()
                        )?;
                    }
                    (src_storage, dst_storage) => {
                        writeln!(
                            self.output,
                            "    mov{} {} [{}]",
                            align,
                            dst_storage.display(),
                            src_storage.display()
                        )?;
                    }
                }
            }
            Instruction::Add(instr) => match_arith!(instr, "add"),
            Instruction::Sub(instr) => match_arith!(instr, "sub"),
            Instruction::Mul(instr) => match_arith!(instr, "mul"),
            Instruction::Shl(instr) => match_arith!(instr, "shl"),
            Instruction::ICmp(instr) => {
                let a = self.parse_operand(None, &instr.operand0, true)?;
                let b = self.parse_operand(None, &instr.operand1, true)?;
                let size = std::cmp::max(a.size, b.size);
                let predicate = match instr.predicate {
                    IntPredicate::EQ => "jeq",
                    IntPredicate::ULT => "jlt",
                    IntPredicate::NE => "jne",
                    _ => todo!(),
                };
                // assert_eq!(a.storage.size(), b.storage.size());
                let dest = self
                    .pool()
                    .get_or_push_stack(instr.dest.to_owned(), OpSize::Byte);
                let true_dest_name = format!(
                    "%__{}_{}_{}_{}_{}_true",
                    self.function_name,
                    instr.dest.clone(),
                    a.name,
                    b.name,
                    predicate
                );
                let false_dest_name = format!(
                    "%__{}_{}_{}_{}_{}_false",
                    self.function_name,
                    instr.dest.clone(),
                    a.name,
                    b.name,
                    predicate
                );
                let end_dest_name = format!(
                    "%__{}_{}_{}_{}_{}_end",
                    self.function_name,
                    instr.dest.clone(),
                    a.name,
                    b.name,
                    predicate
                );
                writeln!(self.output, "; {}", instr)?;
                writeln!(
                    self.output,
                    "    cmp{} {} {}",
                    size,
                    a.storage.display(),
                    b.storage.display()
                )?;
                writeln!(self.output, "    {} q {}", predicate, true_dest_name)?;
                writeln!(self.output, "    jmp q {}", false_dest_name)?;
                writeln!(self.output, "{}", true_dest_name)?;
                writeln!(
                    self.output,
                    "    mov{} {} $1",
                    dest.size,
                    dest.storage.display()
                )?;
                writeln!(self.output, "    jmp q {}", end_dest_name)?;
                writeln!(self.output, "{}", false_dest_name)?;
                writeln!(
                    self.output,
                    "    mov{} {} $0",
                    dest.size,
                    dest.storage.display()
                )?;
                writeln!(self.output, "{}", end_dest_name)?;
            }
            Instruction::ZExt(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let to_type = op_size(&instr.to_type);
                let dst = self
                    .pool()
                    .get_or_push_stack(instr.dest.to_owned(), to_type);

                writeln!(
                    self.output,
                    "    mov{} {} {} ; {}",
                    to_type,
                    dst.storage.display(),
                    src.storage.display(),
                    instr
                )?;
            }
            Instruction::GetElementPtr(instr) => {
                let src = self.parse_operand(None, &instr.address, true)?;
                let dst = self
                    .pool()
                    .get_or_push_stack(instr.dest.to_owned(), src.size);
                let indices: Vec<Ssa> = instr
                    .indices
                    .iter()
                    .map(|ind| self.parse_operand(None, ind, true).unwrap())
                    .collect();
                // assert_eq!(indices.len(), 1);
                // let index = &indices[0];
                writeln!(self.output, "; {}", instr)?;
                let tmp1 = self
                    .pool()
                    .get_unused(src.size, Name::Name("tmp1".to_owned().into()))
                    .unwrap();
                for index in indices.iter() {
                    writeln!(
                        self.output,
                        "    mov{} {} {}",
                        dst.size,
                        tmp1.storage.display(),
                        src.storage.display()
                    )?;
                    writeln!(
                        self.output,
                        "    add{} {} {}",
                        dst.size,
                        tmp1.storage.display(),
                        index.storage.display()
                    )?;
                    writeln!(
                        self.output,
                        "    mov{} {} {}",
                        OpSize::Qword,
                        dst.storage.display(),
                        tmp1.storage.display()
                    )?;
                }
                self.pool().reinsert(tmp1);
            }
            Instruction::Phi(instr) => {
                // "which of these labels did we just come from?"
                let dest = self
                    .pool()
                    .get_or_push_stack(instr.dest.to_owned(), op_size(&instr.to_type));
                let end = self.pool().label(
                    function_name.clone(),
                    format!("%__{}_phi_{}_end", function_name, last_block.name),
                );
                let mut yesses = vec![];
                for (val, label) in instr.incoming_values.iter() {
                    let val = self.parse_operand(None, val, false)?;
                    let label = self.pool().label(function_name.clone(), label.to_string());
                    let yes = self.pool().label(
                        function_name.clone(),
                        format!(
                            "%__{}_phi_{}_{}",
                            function_name.clone(),
                            last_block.name.clone(),
                            label.name.clone()
                        ),
                    );
                    yesses.push((yes.clone(), val.clone()));
                    writeln!(
                        self.output,
                        "    cmp q {} {}",
                        last_block.storage.display(),
                        label.storage.display()
                    )?;
                    writeln!(self.output, "    jeq q {}", yes.storage.display())?;
                }
                writeln!(self.output, "    hlt")?;
                for (yes, val) in yesses.iter() {
                    writeln!(self.output, "{}", yes.storage.display())?;
                    writeln!(
                        self.output,
                        "    mov q {} {}",
                        dest.storage.display(),
                        val.storage.display()
                    )?;
                    writeln!(self.output, "    jmp q {}", end.storage.display())?;
                }

                writeln!(self.output, "{}", end.storage.display())?;
            }
            Instruction::Call(instr) => {
                writeln!(self.output, "; {}", instr)?;
                let func = instr.function.as_ref().unwrap_right();
                let func = self.parse_operand(None, func, false)?;
                let mut args = vec![];
                for (arg, _) in instr.arguments.iter() {
                    args.push(self.parse_operand(None, arg, true)?);
                }
                for (arg, reg) in args.iter().zip(
                    [
                        Storage::Rg,
                        Storage::Rh,
                        Storage::Ri,
                        Storage::Rj,
                        Storage::Rk,
                        Storage::Rl,
                    ][..args.len()]
                        .iter(),
                ) {
                    writeln!(
                        self.output,
                        "    mov{} {} {}",
                        arg.size,
                        reg.display(),
                        arg.storage.display()
                    )?;
                }
                writeln!(self.output, "    call q {}", func.storage.display())?;
            }
            x => {
                println!("WARNING: UNKNOWN INSTRUCTION:    {}", x)
            }
        }
        Ok(())
    }

    pub fn parse_operand(
        &mut self,
        name: Option<Name>,
        op: &Operand,
        assert_exists: bool,
    ) -> Result<Ssa, Box<dyn Error>> {
        let function_name = self.function_name.clone();
        match op {
            Operand::ConstantOperand(con) => {
                let con = &**con;
                let (value, signed) = match con {
                    Constant::Int { bits, value } => {
                        (Literal::from_bits_value(*bits, *value), true)
                    }
                    Constant::GlobalReference { name, ty } => {
                        // println!("{}", name);
                        match &**ty {
                            Type::ArrayType { .. } => {
                                let name = format!("@{}", &name.to_owned().to_string()[1..]);
                                println!("{}", name);
                                println!("{:?}", &name.as_bytes());
                                return Ok(self.pool().get(name).unwrap());
                            }
                            _ => {
                                return Ok(self
                                    .pool()
                                    .label("".into(), name.to_owned().to_string()))
                            }
                        }
                    }
                    Constant::GetElementPtr(instr) => {
                        let dest = self
                            .pool()
                            .push_stack(format!("%{}_getelementptr", function_name), OpSize::Qword);
                        self.parse_instr(&Instruction::GetElementPtr(
                            llvm_ir::instruction::GetElementPtr {
                                address: Operand::ConstantOperand(instr.address.clone()),
                                indices: instr
                                    .indices
                                    .iter()
                                    .map(|ind| Operand::ConstantOperand(ind.to_owned()))
                                    .collect(),
                                dest: dest.name[1..].into(),
                                in_bounds: instr.in_bounds,
                                debugloc: None,
                            },
                        ))?;
                        return Ok(dest);
                    }
                    Constant::Array {
                        element_type,
                        elements,
                    } => {
                        assert_eq!(**element_type, Type::IntegerType { bits: 8 });
                        let mut data = vec![];
                        for elem in elements {
                            match &**elem {
                                Constant::Int { bits, value } => {
                                    assert_eq!(*bits, 8);
                                    data.push(*value as u8);
                                }
                                _ => todo!(),
                            }
                        }
                        let data_label = format!("@{}", &name.unwrap().to_string()[1..]);
                        println!("{}", data_label);
                        println!("{:?}", &data_label.as_bytes());
                        let ssa = Ssa::new(
                            Storage::Data {
                                label: data_label.clone(),
                                data: data.clone(),
                            },
                            Pointer::size(),
                            data_label.to_owned(),
                        );
                        writeln!(
                            self.output,
                            "{} \"{}\"",
                            data_label,
                            std::str::from_utf8(&data).unwrap().trim_end()
                        )?;
                        if let Some(ref mut pool) = self.pool {
                            pool.insert(ssa.clone());
                        }
                        return Ok(ssa);
                    }
                    x => todo!("{}", x),
                };
                Ok(self.pool().constant("constant".to_owned(), value, signed))
            }
            Operand::LocalOperand { name, ty } => {
                if assert_exists {
                    Ok(self.pool().get(name.to_string()).unwrap())
                } else {
                    Ok(self.pool().get_or_push_stack(name.to_owned(), op_size(ty)))
                }
            }
            x => todo!("{}", x),
        }
    }

    pub fn emit_k4sm(&mut self) -> Result<String, Box<dyn Error>> {
        // let mut func_pool = FunctionPool { known_functions: HashMap::new() };
        // for func in self.module.global_aliases.iter() {
        //     println!("{}", func.name);
        //     func_pool.known_functions.insert(func.name.to_owned().into(), Ssa::new(Storage::Label { name: func.name.clone().to_string() }, OpSize::Qword, func.name.clone().into()));
        // }

        let mut globals = HashMap::new();
        for global in self.module.clone().global_vars.iter() {
            let data = self.parse_operand(
                Some(global.name.to_owned()),
                &Operand::ConstantOperand(global.initializer.as_ref().unwrap().to_owned()),
                false,
            )?;
            globals.insert(data.name.clone(), data);
        }

        for func in self.module.clone().functions.iter() {
            writeln!(self.output, "%{}", func.name)?;
            writeln!(self.output, "    push q bp")?;
            writeln!(self.output, "    mov q bp sp")?;
            self.function_name = func.name.to_owned();
            self.pool = Some(RegPool::new(func.parameters.to_owned(), &mut self.output));
            for (_name, global) in globals.iter() {
                println!("found global {}", global.name);
                self.pool().insert(global.clone());
            }
            self.last_block = Some(
                self.pool()
                    .get_unused(OpSize::Word, Name::Name("last_block".to_owned().into()))
                    .unwrap(),
            );
            writeln!(
                self.output,
                "    mov q {} %{}",
                self.last_block.as_ref().unwrap().storage.display(),
                func.name
            )?;
            for block in func.basic_blocks.iter() {
                let block_ssa = self
                    .pool()
                    .label(func.name.clone(), block.name.to_string()[1..].to_owned());
                writeln!(self.output, "{}", block_ssa.storage.display())?;

                // writeln!(self.output, "    pop q {}", last_block.storage.display())?;
                // pool.rel_sp += 8;
                // let mut last_dst = None;
                for instr in block.instrs.iter() {
                    println!();
                    println!("  {}", instr);
                    writeln!(self.output)?;
                    self.parse_instr(instr)?;
                }
                // pool.rel_sp -= 8;
                writeln!(
                    self.output,
                    "    mov q {} {}",
                    self.last_block.as_ref().unwrap().storage.display(),
                    block_ssa.storage.display()
                )?;
                match &block.term {
                    Terminator::Ret(Ret { return_operand, .. }) => {
                        let ret =
                            self.parse_operand(None, return_operand.as_ref().unwrap(), true)?;
                        writeln!(
                            self.output,
                            "    mov{} ra {}",
                            ret.size,
                            ret.storage.display()
                        )?;
                        writeln!(self.output, "    pop q bp")?;
                        writeln!(self.output, "    ret")?;
                    }
                    Terminator::CondBr(CondBr {
                        condition,
                        true_dest,
                        false_dest,
                        ..
                    }) => {
                        let cond = self.parse_operand(None, condition, true)?;
                        let true_dest = self
                            .pool()
                            .label(func.name.clone(), true_dest.to_owned().to_string());
                        let false_dest = self
                            .pool()
                            .label(func.name.clone(), false_dest.to_owned().to_string());
                        writeln!(
                            self.output,
                            "    cmp{} {} $0",
                            cond.size,
                            cond.storage.display()
                        )?;
                        writeln!(self.output, "    jeq q {}", false_dest.storage.display())?;
                        writeln!(self.output, "    jmp q {}", true_dest.storage.display())?;
                    }
                    Terminator::Br(Br { dest, .. }) => {
                        let dest = self.pool().label(func.name.clone(), dest.to_string());
                        writeln!(self.output, "    jmp q {}", dest.storage.display())?;
                    }
                    x => todo!("{}", x),
                };
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
