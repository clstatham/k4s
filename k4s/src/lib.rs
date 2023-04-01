use std::collections::{BTreeMap, HashMap};

pub const HEADER_MAGIC: &[u8] = b"k4d\x13\x37";
pub const HEADER_ENTRY_POINT: &[u8] = b"ent";
pub const HEADER_END: &[u8] = b"\x69\x69d4k";

pub const LIT: u8 = 0xff;

bitflags::bitflags! {
    pub struct ValidOpArgs: u16 {
        const NOARGS =   0b1;
        const VAL =      0b10;
        const ADR =      0b100;
        const VAL_VAL =  0b1000;
        const VAL_ADR =  0b10000;
        const ADR_VAL =  0b100000;
        const ADR_ADR =  0b1000000;
    }
}

impl ValidOpArgs {
    pub fn str_reps(&self) -> Vec<&'static str> {
        let mut out = vec![];
        if self.contains(Self::VAL) {
            out.push("a");
        }
        if self.contains(Self::ADR) {
            out.push("[a]");
        }
        if self.contains(Self::VAL_VAL) {
            out.push("a a");
        }
        if self.contains(Self::VAL_ADR) {
            out.push("a [a]");
        }
        if self.contains(Self::ADR_VAL) {
            out.push("[a] a");
        }
        if self.contains(Self::ADR_ADR) {
            out.push("[a] [a]");
        }
        out
    }
}

pub fn valid_ops() -> BTreeMap<&'static str, ValidOpArgs> {
    let mut ops = BTreeMap::new();
    ops.insert("nop", ValidOpArgs::NOARGS);
    ops.insert("hlt", ValidOpArgs::NOARGS);
    ops.insert("ret", ValidOpArgs::NOARGS);
    ops.insert(
        "mov",
        ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL | ValidOpArgs::ADR_ADR,
    );
    ops.insert("push", ValidOpArgs::VAL | ValidOpArgs::ADR);
    ops.insert("pop", ValidOpArgs::VAL | ValidOpArgs::ADR);
    ops.insert("printi", ValidOpArgs::VAL | ValidOpArgs::ADR);
    ops.insert("printc", ValidOpArgs::VAL | ValidOpArgs::ADR);
    ops.insert("add", ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR);
    ops.insert("sub", ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR);
    ops.insert("mul", ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR);
    ops.insert("div", ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR);
    ops.insert("mod", ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR);
    ops.insert("and", ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR);
    ops.insert("or", ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR);
    ops.insert("xor", ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR);
    ops.insert(
        "cmp",
        ValidOpArgs::VAL_VAL | ValidOpArgs::VAL_ADR | ValidOpArgs::ADR_VAL,
    );
    ops.insert("jmp", ValidOpArgs::VAL);
    ops.insert("jgt", ValidOpArgs::VAL);
    ops.insert("jlt", ValidOpArgs::VAL);
    ops.insert("jeq", ValidOpArgs::VAL);
    ops.insert("jne", ValidOpArgs::VAL);
    ops.insert("call", ValidOpArgs::VAL);
    ops.insert("not", ValidOpArgs::VAL);
    ops.insert("shl", ValidOpArgs::VAL_VAL);
    ops.insert("shr", ValidOpArgs::VAL_VAL);
    ops
}

pub fn gen_bytecodes() -> HashMap<String, u8> {
    let mut out = HashMap::new();
    let mut i: u8 = 0;
    for (op, args) in valid_ops() {
        let str_reps = args.str_reps();
        if str_reps.is_empty() {
            let pattern = op.to_owned();
            out.insert(pattern, i);
            i = i.checked_add(1).expect("Too many op variants!");
        } else {
            for variant in str_reps {
                let mut pattern = op.to_owned();
                pattern.push(' ');
                pattern.push_str(variant);
                out.insert(pattern, i);
                i = i.checked_add(1).expect("Too many op variants!");
            }
        }
    }
    out
}

pub fn gen_regs() -> HashMap<&'static str, u8> {
    [
        "ra", "rb", "rc", "rd", "re", "rf", "rg", "rh", "ri", "rj", "rk", "rl", "bp", "sp", "pc",
        "fl",
    ]
    .into_iter()
    .enumerate()
    .map(|(i, reg)| (reg, i.try_into().unwrap()))
    .collect()
}
