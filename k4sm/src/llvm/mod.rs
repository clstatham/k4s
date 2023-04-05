use std::{
    collections::HashMap,
    error::Error,
    fmt::Write,
    path::Path,
    sync::atomic::{AtomicUsize, Ordering}, rc::Rc,
};

use k4s::{InstructionSize, Literal};
use llvm_ir::{
    terminator::{Br, CondBr, Ret},
    Constant, Instruction, IntPredicate, Module, Name, Operand, Terminator, Type,
};

use crate::llvm::ssa::Register;

use self::{regpool::RegPool, ssa::Ssa};

pub mod regpool;
pub mod ssa;

#[inline]
pub fn op_size(typ: &Type) -> InstructionSize {
    match typ {
        Type::IntegerType { bits } => match *bits {
            1 => InstructionSize::Byte, // boolean
            8 => InstructionSize::Byte,
            16 => InstructionSize::Word,
            32 => InstructionSize::Dword,
            64 => InstructionSize::Qword,
            x => unreachable!("integer bits {}", x),
        },
        Type::PointerType { .. } => InstructionSize::Qword,
        Type::ArrayType { .. } => todo!(),
        Type::StructType { .. } => InstructionSize::Unsized,
        Type::NamedStructType { .. } => InstructionSize::Unsized,
        Type::FPType(precision) => match precision {
            llvm_ir::types::FPType::Single => InstructionSize::Dword,
            llvm_ir::types::FPType::Double => InstructionSize::Qword,
            t => todo!("{:?}", t),
        },
        t => todo!("{:?}", t),
    }
}

#[derive(Default)]
pub struct Function {
    name: String,

    prologue: String,
    body: String,
    epilogue: String,

    pool: RegPool,
    last_block: Option<Rc<Ssa>>,

    label_count: usize,
}

pub struct Parser {
    module: Module,
    output: String,

    anon_datas: AtomicUsize,
    current_function: Function,
}

impl Parser {
    pub fn new(bc_path: impl AsRef<Path>) -> Self {
        Self {
            module: Module::from_bc_path(bc_path).unwrap(),
            output: String::new(),
            anon_datas: AtomicUsize::new(0),
            current_function: Function::default(),
        }
    }

    pub fn function_name(&self) -> String {
        self.current_function.name.clone()
    }

    pub fn pool(&mut self) -> &mut RegPool {
        &mut self.current_function.pool
    }

    fn parse_instr(&mut self, instr: &Instruction) -> Result<(), Box<dyn Error>> {
        macro_rules! match_arith {
            ($instr:expr, $mn:literal) => {{
                let a = self.parse_operand(None, &$instr.operand0, true)?;
                let b = self.parse_operand(None, &$instr.operand1, true)?;
                assert_eq!(a.size(), b.size());
                let dst = self.get_or_push_literal(
                    &$instr.dest.to_string(),
                    Literal::default_for_size(a.size()),
                );

                writeln!(&mut self.current_function.body, "; {}", $instr)?;
                writeln!(
                    &mut self.current_function.body,
                    "    mov{} {} {}",
                    dst.size(),
                    dst.display(),
                    a.display()
                )?;
                writeln!(
                    &mut self.current_function.body,
                    concat!("    ", $mn, "{} {} {}"),
                    dst.size(),
                    dst.display(),
                    b.display()
                )?;
            }};
        }
        let function_name = self.function_name();
        let last_block = self.current_function.last_block.as_ref().unwrap().clone();
        writeln!(self.current_function.body, "; {}", instr)?;
        match instr {
            Instruction::Alloca(instr) => {
                // this is a pointer
                let count = self.parse_operand(None, &instr.num_elements, false)?;
                let count = if let Ssa::Constant { value, .. } = count.as_ref() {
                    value.as_qword().get() as usize
                } else {
                    todo!("{:?}", count)
                };
                assert_eq!(count, 1);

                let ssa = Ssa::push(
                    &instr.allocated_type,
                    format!("{}_pointee", &instr.dest.to_string()),
                    &self.module.types.to_owned(),
                    self.pool(),
                );
                let off = self.pool().stack_size;
                let ptr = self
                    .pool()
                    .push_pointer(&instr.dest.to_string(), ssa);
                let tmp = self
                    .pool()
                    .get_unused("tmp", InstructionSize::Qword)
                    .unwrap();
                writeln!(self.current_function.body, "    mov q {} bp", tmp)?;
                writeln!(self.current_function.body, "    sub q {} ${}", tmp, off)?;
                writeln!(self.current_function.body, "    mov q {} {}", ptr, tmp)?;
                self.pool().take_back("tmp", tmp);
            }
            Instruction::Store(instr) => {
                let dst = self.parse_operand(None, &instr.address, true)?;
                let src = self.parse_operand(None, &instr.value, true)?;
                match (src.stack_offset(), dst.stack_offset()) {
                    (Some(_), Some(_)) => {
                        let tmp1 = self
                            .pool()
                            .get_unused("tmp1", InstructionSize::Qword)
                            .unwrap();
                        writeln!(self.current_function.body, "; [{}] <= {}", dst, src)?;
                        writeln!(self.current_function.body, "    mov q {} {}", tmp1, dst,)?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            InstructionSize::Qword,
                            tmp1,
                            src
                        )?;
                        self.pool().take_back("tmp1", tmp1);
                    }
                    (Some(_), None) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            InstructionSize::Qword,
                            dst,
                            src
                        )?;
                    }
                    (None, Some(_)) => {
                        let tmp1 = self
                            .pool()
                            .get_unused("tmp1", InstructionSize::Qword)
                            .unwrap();
                        writeln!(self.current_function.body, "; [{}] <= {}", dst, src)?;
                        writeln!(self.current_function.body, "    mov q {} {}", tmp1, dst,)?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            InstructionSize::Qword,
                            tmp1,
                            src
                        )?;
                        self.pool().take_back("tmp1", tmp1);
                    }
                    (None, None) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} [{}] {}",
                            dst.size(),
                            dst,
                            src
                        )?;
                    }
                }
            }
            Instruction::Load(instr) => {
                let src = self.parse_operand(None, &instr.address, true)?;
                let dst = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(src.size()),
                );

                let align = InstructionSize::from_n_bytes(instr.alignment);
                match (src.stack_offset(), dst.stack_offset()) {
                    (Some(src_off), Some(dst_off)) => {
                        let tmp = self
                            .pool()
                            .get_unused("tmp", InstructionSize::Qword)
                            .unwrap();
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [-{}+bp]",
                            InstructionSize::Qword,
                            tmp,
                            src_off
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} [-{}+bp] [{}]",
                            InstructionSize::Qword,
                            dst_off,
                            tmp
                        )?;
                        self.pool().take_back("tmp", tmp);
                    }
                    (Some(src_off), None) => {
                        let tmp = self
                            .pool()
                            .get_unused("tmp", InstructionSize::Qword)
                            .unwrap();
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [-{}+bp]",
                            InstructionSize::Qword,
                            tmp,
                            src_off
                        )?;
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [{}]",
                            dst.size(),
                            dst,
                            tmp
                        )?;
                        self.pool().take_back("tmp", tmp);
                    }
                    (None, Some(dst_off)) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} [-{}+bp] [{}]",
                            align, dst_off, src
                        )?;
                    }
                    (None, None) => {
                        writeln!(
                            self.current_function.body,
                            "    mov{} {} [{}]",
                            dst.size(),
                            dst,
                            src
                        )?;
                    }
                }
            }
            Instruction::Add(instr) => match_arith!(instr, "add"),
            Instruction::Sub(instr) => match_arith!(instr, "sub"),
            Instruction::Mul(instr) => match_arith!(instr, "mul"),
            Instruction::Shl(instr) => match_arith!(instr, "shl"),
            Instruction::LShr(instr) => match_arith!(instr, "shr"),
            Instruction::Or(instr) => match_arith!(instr, "or"),
            Instruction::And(instr) => match_arith!(instr, "and"),
            Instruction::Xor(instr) => match_arith!(instr, "xor"),

            Instruction::ICmp(instr) => {
                let a = self.parse_operand(None, &instr.operand0, true)?;
                let b = self.parse_operand(None, &instr.operand1, true)?;
                let size = std::cmp::max(a.size(), b.size());
                let predicate = match instr.predicate {
                    IntPredicate::EQ => "jeq",
                    IntPredicate::ULT | IntPredicate::SLT => "jlt",
                    IntPredicate::UGT | IntPredicate::SGT => "jgt",
                    IntPredicate::NE => "jne",
                    _ => todo!(),
                };
                let comparison = match instr.predicate {
                    IntPredicate::SGE | IntPredicate::SLE => "scmp",
                    _ => "cmp",
                };
                let label_id = self.current_function.label_count;
                let dest = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(InstructionSize::Byte),
                );
                let id = self.anon_datas.fetch_add(1, Ordering::SeqCst);
                let true_dest_name = format!("__{label_id}_cmp_true{}", id);
                let false_dest_name = format!("__{label_id}_cmp_false{}", id);
                let end_dest_name = format!("__{label_id}_cmp_end{}", id);
                let true_dest = self.pool().label(&function_name, &true_dest_name);
                let false_dest = self.pool().label(&function_name, &false_dest_name);
                let end_dest = self.pool().label(&function_name, &end_dest_name);

                writeln!(
                    self.current_function.body,
                    "    {}{} {} {}",
                    comparison, size, a, b
                )?;
                writeln!(
                    self.current_function.body,
                    "    {} q {}",
                    predicate, true_dest
                )?;
                writeln!(self.current_function.body, "    jmp q {}", false_dest)?;
                writeln!(self.current_function.body, "{}", true_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} $1",
                    dest.size(),
                    dest
                )?;
                writeln!(self.current_function.body, "    jmp q {}", end_dest)?;
                writeln!(self.current_function.body, "{}", false_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} rz",
                    dest.size(),
                    dest
                )?;
                writeln!(self.current_function.body, "{}", end_dest)?;
            }
            Instruction::Select(instr) => {
                let cond = self.parse_operand(None, &instr.condition, true)?;
                let true_val = self.parse_operand(None, &instr.true_value, false)?;
                let false_val = self.parse_operand(None, &instr.false_value, false)?;
                let dest = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(InstructionSize::Byte),
                );

                let id = self.anon_datas.fetch_add(1, Ordering::SeqCst);
                let true_dest_name = format!("__select_true{}", id);
                let false_dest_name = format!("__select_true{}", id);
                let end_dest_name = format!("__select_end{}", id);
                let true_dest = self.pool().label(&function_name, &true_dest_name);
                let false_dest = self.pool().label(&function_name, &false_dest_name);
                let end_dest = self.pool().label(&function_name, &end_dest_name);

                writeln!(self.current_function.body, "    cmp b {} rz", cond)?;
                writeln!(self.current_function.body, "    jne q {}", true_dest)?;
                writeln!(self.current_function.body, "    jmp q {}", false_dest)?;
                writeln!(self.current_function.body, "{}", true_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dest.size(),
                    dest,
                    true_val
                )?;
                writeln!(self.current_function.body, "    jmp q {}", end_dest)?;
                writeln!(self.current_function.body, "{}", false_dest)?;
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    dest.size(),
                    dest,
                    false_val
                )?;
                writeln!(self.current_function.body, "    jmp q {}", end_dest)?;
                writeln!(self.current_function.body, "{}", end_dest)?;
            }
            Instruction::ZExt(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let to_type = op_size(&instr.to_type);
                let dst = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(to_type),
                );

                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    to_type, dst, src,
                )?;
            }
            Instruction::Trunc(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let to_type = op_size(&instr.to_type);
                let dst = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(to_type),
                );

                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    to_type, dst, src,
                )?;
            }
            Instruction::BitCast(instr) => {
                let src = self.parse_operand(None, &instr.operand, true)?;
                let to_type = op_size(&instr.to_type);
                let dst = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(to_type),
                );

                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    to_type, dst, src,
                )?;
            }
            Instruction::GetElementPtr(instr) => {
                let dst = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(InstructionSize::Qword),
                );
                let indices: Vec<_> = instr
                    .indices
                    .iter()
                    .map(|ind| self.parse_operand(None, ind, true).unwrap())
                    .collect();

                let src = self.parse_operand(None, &instr.address, true)?;
                let offset = self.get_element_ptr(src, indices)?;

                writeln!(self.current_function.body, "    mov q {} bp", dst)?;
                writeln!(self.current_function.body, "    sub q {} {}", dst, offset)?;
            }
            Instruction::Phi(instr) => {
                // "which of these labels did we just come from?"
                let label_id = self.current_function.label_count;
                let dest = self.get_or_push_literal(
                    &instr.dest.to_string(),
                    Literal::default_for_size(op_size(&instr.to_type)),
                );
                let end = self
                    .pool()
                    .label(&function_name, &format!("%__{}_phi_end", label_id));
                let mut yesses = vec![];
                for (val, label) in instr.incoming_values.iter() {
                    let val = self.parse_operand(None, val, false)?;
                    let label = self.pool().label(&function_name, &label.to_string());
                    let yes = self
                        .pool()
                        .label(&function_name, &format!("__{}_phi_{}", label_id, label));
                    yesses.push((yes.clone(), val.clone()));
                    writeln!(
                        self.current_function.body,
                        "    cmp q {} {}",
                        last_block, label
                    )?;
                    writeln!(self.current_function.body, "    jeq q {}", yes)?;
                }
                writeln!(self.current_function.body, "    und")?;
                for (yes, val) in yesses.iter() {
                    writeln!(self.current_function.body, "{}", yes)?;
                    writeln!(self.current_function.body, "    mov q {} {}", dest, val)?;
                    writeln!(self.current_function.body, "    jmp q {}", end)?;
                }

                writeln!(self.current_function.body, "{}", end)?;

                self.current_function.label_count += 1;
            }
            Instruction::Call(instr) => {
                let func = instr.function.as_ref().unwrap_right();
                let func = self.parse_operand(None, func, false)?;
                let mut args = vec![];
                for (arg, _) in instr.arguments.iter() {
                    args.push(self.parse_operand(None, arg, true)?);
                }
                let dest = instr.dest.as_ref().map(|dest| {
                    self.get_or_push_literal(
                        &dest.to_string(),
                        Literal::default_for_size(func.size()),
                    )
                });
                for (arg, reg) in args.iter().zip(
                    [
                        Register::Rg,
                        Register::Rh,
                        Register::Ri,
                        Register::Rj,
                        Register::Rk,
                        Register::Rl,
                    ][..args.len()]
                        .iter(),
                ) {
                    writeln!(
                        self.current_function.body,
                        "    mov{} {} {}",
                        arg.size(),
                        reg.display(),
                        arg
                    )?;
                }
                writeln!(self.current_function.body, "    call q {}", func)?;
                if let Some(dest) = dest {
                    writeln!(
                        self.current_function.body,
                        "    mov{} {} ra",
                        dest.size(),
                        dest
                    )?;
                }
            }
            Instruction::InsertValue(instr) => {
                let val = self.parse_operand(None, &instr.element, false)?;
                let indices = instr
                    .indices
                    .iter()
                    .map(|index| Rc::new(Ssa::Constant {
                        name: format!("index_{}", self.anon_datas.fetch_add(1, Ordering::SeqCst)),
                        value: Literal::Dword((*index).into()),
                        signed: false,
                    }))
                    .collect::<Vec<_>>();
                let agg = self.parse_operand(None, &instr.aggregate, true)?;
                let dst = agg.duplicate(&instr.dest.to_string());

                self.pool().insert(dst.clone());
                let ptr = self.get_element_ptr(dst, indices)?;
                let tmp = self
                    .pool()
                    .get_unused("tmp", InstructionSize::Qword)
                    .unwrap();
                writeln!(
                    self.current_function.body,
                    "    mov{} {} {}",
                    tmp.size(),
                    tmp,
                    ptr
                )?;
                writeln!(
                    self.current_function.body,
                    "    mov{} [{}] {}",
                    val.size(),
                    tmp,
                    val
                )?;
                self.pool().take_back(&tmp.name(), tmp);
            }

            x => {
                panic!("UNKNOWN INSTRUCTION:    {}", x)
            }
        }
        Ok(())
    }

    fn get_element_ptr_const(
        &mut self,
        mut src: Rc<Ssa>,
        indices: Vec<Rc<Ssa>>,
    ) -> Result<Rc<Ssa>, Box<dyn Error>> {
        let mut offset = 0;
        for index in indices.iter() {
            let index = if let Ssa::Constant { value, .. } = index.as_ref() {
                value.as_qword().get() as usize
            } else if let Ssa::Register {
                reg: Register::Rz, ..
            } = index.as_ref()
            {
                0
            } else {
                todo!("{:?}", index)
            };

            match src.as_ref() {
                Ssa::Composite {
                    stack_offset,
                    ref elements,
                    ..
                } => {
                    offset = *stack_offset;
                    for elem in &elements[..index] {
                        offset -= elem.size_in_bytes();
                    }

                    // todo: how do we assign `src` to the element at `index`?
                }
                Ssa::Pointer {
                    stack_offset: _,
                    pointee,
                    ..
                } => {
                    assert_eq!(index, 0, "Attempt to index further than 0 into a pointer");

                    src = pointee.clone();
                }
                _ => {}
            }
        }

        let offset = Rc::new(Ssa::Constant {
            name: format!("{}_offset", src.name()),
            value: Literal::Qword((offset as u64).into()),
            signed: false,
        });
        Ok(offset)
    }

    fn get_element_ptr(&mut self, mut src: Rc<Ssa>, indices: Vec<Rc<Ssa>>) -> Result<Rc<Ssa>, Box<dyn Error>> {
        let id = self.anon_datas.fetch_add(1, Ordering::SeqCst);
        let offset = self.pool().push_literal(
            &format!("{}_offset_{}", src.name(), id),
            Literal::default_for_size(InstructionSize::Qword),
            false,
        );
        if let Some(off) = src.stack_offset() {
            writeln!(self.current_function.body, "    mov q {} ${}", offset, off)?;
        }
        for index in indices.iter() {
            match src.as_ref() {
                Ssa::Composite {
                    stack_offset,
                    ref elements,
                    ..
                } => {
                    let counter = self
                        .pool()
                        .get_unused("counter", InstructionSize::Qword)
                        .unwrap();
                    writeln!(self.current_function.body, "    mov q {} rz", counter)?;

                    // our task here:
                    // loop {
                    //     compare the counter to the index
                    //     if equal, break the loop
                    //     else {
                    //         subtract the size of the element to the offset (goes backwards)
                    //         increment counter by 1
                    //     }
                    // }
                    // *** this will need to be an unrolled loop in the assembly code, unfortunately, but we can use a for loop here
                    let id = self.anon_datas.fetch_add(1, Ordering::SeqCst);
                    let func_name = self.current_function.name.to_owned();
                    let end_label = self.pool().label(
                        &func_name,
                        &format!("_struct_index_{}_end_{}", src.name(), id),
                    );
                    for elem in elements {
                        writeln!(
                            self.current_function.body,
                            "    cmp q {} {}",
                            counter, index
                        )?;
                        writeln!(self.current_function.body, "    jeq q {}", end_label)?;
                        writeln!(
                            self.current_function.body,
                            "    sub q {} ${}",
                            offset,
                            elem.size_in_bytes()
                        )?;
                        writeln!(self.current_function.body, "    add q {} $1", counter)?;
                    }
                    writeln!(self.current_function.body, "{}", end_label)?;

                    self.pool().take_back(&counter.name(), counter);
                }
                Ssa::Pointer {
                    stack_offset: _,
                    pointee,
                    ..
                } => {
                    if let Ssa::Register {
                        reg: Register::Rz, ..
                    } = index.as_ref()
                    {
                        // fast path
                        // index of 0, we don't add anything
                    } else {
                        todo!()
                    }

                    src = pointee.clone();
                }
                _ => {}
            }
        }
        Ok(offset)
    }

    pub fn parse_operand(
        &mut self,
        name: Option<Name>,
        op: &Operand,
        assert_exists: bool,
    ) -> Result<Rc<Ssa>, Box<dyn Error>> {
        if let Some(ref name) = name {
            if let Some(ssa) = self.pool().get(&name.to_string()) {
                return Ok(ssa);
            }
        }
        match op {
            Operand::ConstantOperand(con) => {
                let con = &**con;
                match con {
                    Constant::Int { bits, value } => {
                        if *value == 0 {
                            Ok(Rc::new(Ssa::Register {
                                name: "rz".to_owned(),
                                reg: Register::Rz,
                                size: InstructionSize::from_n_bytes(1.max(*bits / 8)),
                            }))
                        } else {
                            let (value, signed) = (Literal::from_bits_value(*bits, *value), true);
                            Ok(Rc::new(Ssa::Constant {
                                name: name
                                    .as_ref()
                                    .map(|name| name.to_string())
                                    .unwrap_or(format!("{}", value.as_qword())),
                                value,
                                signed,
                            }))
                        }
                    }
                    Constant::GlobalReference { name, ty } => {
                        if let Some(ssa) = self.pool().get(&name.to_string()) {
                            return Ok(ssa);
                        }
                        match &**ty {
                            Type::ArrayType { .. } => {
                                let name = format!("@{}", &name.to_string()[1..]);
                                return Ok(self.pool().get(&name).unwrap());
                            }
                            Type::LabelType => return Ok(self.pool().label("", &name.to_string())),
                            Type::FuncType { .. } => {
                                return Ok(self.pool().label("", &name.to_string()))
                            }
                            Type::StructType { .. } => {
                                let ssa = Ssa::parse_const(
                                    ty,
                                    name.to_string(),
                                    &self.module.types.clone(),
                                    self.pool(),
                                );

                                Ok(ssa)
                            }
                            Type::NamedStructType { name } => {
                                let struc = self.module.types.named_struct(name);
                                let ssa = Ssa::parse_const(
                                    &struc,
                                    name.to_string(),
                                    &self.module.types.clone(),
                                    self.pool(),
                                );
                                dbg!(ssa);
                                todo!()
                            }
                            ty => {
                                todo!("{:?}", ty)
                            }
                        }
                    }
                    Constant::GetElementPtr(instr) => {
                        let indices = instr
                            .indices
                            .iter()
                            .map(|ind| {
                                self.parse_operand(
                                    None,
                                    &Operand::ConstantOperand(ind.to_owned()),
                                    false,
                                )
                                .unwrap()
                            })
                            .collect();
                        
                        let src = self.parse_operand(None, &Operand::ConstantOperand(instr.address.clone()), true)?;
                        let offset = self.get_element_ptr_const(
                            src,
                            indices,
                        )?;
                        self.pool().insert(offset.clone());
                        Ok(offset)
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
                        let data_label = format!(
                            "@{}",
                            &name
                                .unwrap_or(
                                    format!(
                                        "anon_data_{}",
                                        self.anon_datas.fetch_add(1, Ordering::SeqCst)
                                    )
                                    .into()
                                )
                                .to_string()[1..]
                        );
                        let ssa = Rc::new(Ssa::Data {
                            label: data_label.clone(),
                            data: data.clone(),
                        });
                        writeln!(
                            self.output,
                            "{} \"{}\"",
                            data_label,
                            data.iter()
                                .map(|byte| format!("\\x{:x}", byte))
                                .collect::<Vec<_>>()
                                .join("")
                        )?;
                        self.current_function.pool.insert(ssa.clone());
                        Ok(ssa)
                    }
                    Constant::Struct {
                        name: struc_name,
                        values,
                        is_packed,
                    } => {
                        let name = struc_name
                            .as_ref()
                            .cloned()
                            .or(name.map(|name| name.to_string()))
                            .unwrap_or(format!(
                                "const_struct_{}",
                                self.anon_datas.fetch_add(1, Ordering::SeqCst)
                            ));
                        let mut elements = vec![];
                        writeln!(self.output, "{}", name)?;
                        let name = name.strip_prefix('%').unwrap_or(&name).to_owned();
                        let top_label = self.pool().label("", &name);
                        for (i, value) in values.iter().enumerate() {
                            let val = self.parse_operand(
                                Some(format!("{}_elem{}", name, i).into()),
                                &Operand::ConstantOperand(value.to_owned()),
                                false,
                            )?;
                            elements.push(val);
                        }

                        Ok(top_label)
                    }
                    Constant::BitCast(cast) => {
                        let operand = self.parse_operand(
                            None,
                            &Operand::ConstantOperand(cast.operand.to_owned()),
                            false,
                        )?;
                        match (operand.as_ref(), &*cast.to_type) {
                            // these are all basically TODO but i want to see if it breaks anything first
                            (Ssa::Label { .. }, Type::PointerType { .. }) => Ok(operand),
                            (Ssa::Data { .. }, Type::PointerType { .. }) => Ok(operand),
                            (Ssa::StaticComposite { .. }, Type::PointerType { .. }) => Ok(operand),
                            t => todo!("{:#?}", t),
                        }
                    }
                    Constant::AggregateZero(typ) => {
                        let data_label = format!(
                            "{}",
                            &name
                                .unwrap_or(
                                    format!(
                                        "anon_data_{}",
                                        self.anon_datas.fetch_add(1, Ordering::SeqCst)
                                    )
                                    .into()
                                )
                                .to_string()[1..]
                        );
                        let label = self.pool().label("", &data_label);
                        let ssa = Ssa::parse_const(
                            typ,
                            data_label.clone(),
                            &self.module.types.to_owned(),
                            self.pool(),
                        );
                        let size_bytes = ssa.size_in_bytes();
                        writeln!(self.output, "{}", label)?;
                        writeln!(
                            self.output,
                            "@{}_init resb {}",
                            data_label,
                            size_bytes,
                        )?;
                        self.current_function.pool.insert(ssa.clone());
                        Ok(ssa)
                    }
                    Constant::Null(_) => {
                        let data_label = format!(
                            "@{}",
                            &name
                                .unwrap_or(
                                    format!(
                                        "null_data_{}",
                                        self.anon_datas.fetch_add(1, Ordering::SeqCst)
                                    )
                                    .into()
                                )
                                .to_string()[1..]
                        );
                        let ssa = Rc::new(Ssa::NullPointer { label: data_label });
                        self.pool().insert(ssa.clone());
                        writeln!(self.output, "{} $0", ssa)?;
                        Ok(ssa)
                    }
                    Constant::Undef(und) => {
                        let ssa = Rc::new(Ssa::Undef {
                            name: format!(
                                "undef_{}_{}",
                                op_size(und),
                                self.anon_datas.fetch_add(1, Ordering::SeqCst)
                            ),
                            size: op_size(und),
                        });
                        self.pool().insert(ssa.clone());
                        Ok(ssa)
                    }
                    x => todo!("{}", x),
                }
            }
            Operand::LocalOperand { name, ty } => {
                if assert_exists {
                    Ok(self
                        .pool()
                        .get(&name.to_string())
                        .unwrap_or_else(|| panic!("{:?} {:?}", name.to_string(), ty)))
                } else {
                    Ok(self.get_or_push_literal(
                        &name.to_string(),
                        Literal::default_for_size(op_size(ty)),
                    ))
                }
            }
            x => todo!("{}", x),
        }
    }

    fn get_or_push_literal(&mut self, name: &str, value: Literal) -> Rc<Ssa> {
        if let Some(ssa) = self.pool().get(name) {
            ssa
        } else {
            self.pool().push_literal(name, value, false)
        }
    }

    pub fn emit_k4sm(&mut self) -> Result<String, Box<dyn Error>> {
        let mut globals = HashMap::new();
        for global in self.module.clone().global_vars.iter() {
            let data = self.parse_operand(
                Some(global.name.to_owned()),
                &Operand::ConstantOperand(global.initializer.as_ref().unwrap().to_owned()),
                false,
            )?;
            globals.insert(data.display(), data);
        }

        writeln!(self.output)?;

        self.current_function = Function::default();

        for func in self.module.clone().functions.iter() {
            println!();
            self.current_function = Function::default();
            writeln!(self.current_function.prologue, "%{}", func.name)?;
            writeln!(self.current_function.prologue, "    push q bp")?;
            writeln!(self.current_function.prologue, "    mov q bp sp")?;

            self.current_function.name = func.name.to_owned();
            self.current_function.pool =
                RegPool::new(func.parameters.to_owned(), &mut self.current_function.body);
            for (_name, global) in globals.iter() {
                self.pool().insert(global.clone());
            }
            self.current_function.last_block = Some(
                self.pool()
                    .get_unused("last_block", InstructionSize::Qword)
                    .unwrap(),
            );
            writeln!(
                self.current_function.body,
                "    mov q {} %{}",
                self.current_function.last_block.as_ref().unwrap().display(),
                func.name
            )?;
            println!("Function {}", self.current_function.name);
            for block in func.basic_blocks.iter() {
                let block_ssa = self.pool().label(&func.name, &block.name.to_string()[1..]);
                writeln!(self.current_function.body, "{}", block_ssa)?;

                for instr in block.instrs.iter() {
                    println!("  {}", instr);
                    self.parse_instr(instr)?;
                }
                writeln!(
                    self.current_function.body,
                    "    mov q {} {}",
                    self.current_function.last_block.as_ref().unwrap().display(),
                    block_ssa
                )?;
                match &block.term {
                    Terminator::Ret(Ret { return_operand, .. }) => {
                        if let Some(ret) = return_operand.as_ref() {
                            let ret = self.parse_operand(None, ret, true)?;
                            writeln!(
                                self.current_function.epilogue,
                                "    mov{} ra {}",
                                ret.size(),
                                ret
                            )?;
                        }
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
                            .label(&func.name, &true_dest.to_owned().to_string());
                        let false_dest = self
                            .pool()
                            .label(&func.name, &false_dest.to_owned().to_string());
                        writeln!(
                            self.current_function.body,
                            "    cmp{} {} rz",
                            cond.size(),
                            cond
                        )?;
                        writeln!(self.current_function.body, "    jeq q {}", false_dest)?;
                        writeln!(self.current_function.body, "    jmp q {}", true_dest)?;
                    }
                    Terminator::Br(Br { dest, .. }) => {
                        let dest = self.pool().label(&func.name, &dest.to_string());
                        writeln!(self.current_function.body, "    jmp q {}", dest)?;
                    }
                    Terminator::Unreachable(_) => {
                        writeln!(self.current_function.body, "    und")?;
                    }
                    Terminator::Switch(switch) => {
                        let op = self.parse_operand(None, &switch.operand, true)?;
                        for (opt, dest) in switch.dests.iter() {
                            let opt = self.parse_operand(
                                None,
                                &Operand::ConstantOperand(opt.to_owned()),
                                false,
                            )?;
                            let dest = self.pool().label(&func.name, &dest.to_string());
                            writeln!(
                                self.current_function.body,
                                "    cmp{} {} {}",
                                op.size(),
                                op,
                                opt
                            )?;
                            writeln!(self.current_function.body, "    jeq q {}", dest)?;
                        }
                        let default = self
                            .pool()
                            .label(&func.name, &switch.default_dest.to_string());
                        writeln!(self.current_function.body, "    jmp q {}", default)?;
                    }
                    x => todo!("{}", x),
                };
            }

            let sp = self.pool().stack_size;
            if sp != 0 {
                writeln!(self.current_function.prologue, "    sub q sp ${}", sp)?;
                writeln!(self.current_function.epilogue, "    add q sp ${}", sp)?;
            }

            writeln!(self.current_function.epilogue, "    pop q bp")?;
            writeln!(self.current_function.epilogue, "    ret")?;

            write!(self.output, "{}", self.current_function.prologue)?;
            write!(self.output, "{}", self.current_function.body)?;
            writeln!(self.output, "{}", self.current_function.epilogue)?;
        }

        Ok(self.output.clone())
    }
}
