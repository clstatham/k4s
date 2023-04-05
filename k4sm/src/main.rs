#![allow(clippy::useless_format)]

use std::{
    collections::HashMap,
    env::args,
    error::Error,
    fmt::Display,
    fs::File,
    io::{Read, Write},
    mem::size_of,
    str::Lines, path::PathBuf,
};

use k4s::*;
use nom::sequence::tuple;

use crate::llvm::Parser;

pub mod llvm;
pub mod tests;

#[derive(Debug)]
pub struct AssemblyError(String);
impl Display for AssemblyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl Error for AssemblyError {}

#[derive(Clone)]
pub struct Data {
    loc: u64,
    data: Vec<u8>,
}

pub struct Assembler<'a> {
    entry_point: u64,
    pc: u64,
    labels: HashMap<String, u64>,
    label_refs: HashMap<String, Vec<u64>>,
    datas: HashMap<String, Data>,
    data_refs: HashMap<String, Vec<u64>>,
    header: Vec<u8>,
    includes: HashMap<String, String>,
    output: Vec<u8>,
    input_lines: Lines<'a>,
    current_line: usize,
}

impl<'a> Assembler<'a> {
    pub fn new(input: &'a str, default_entry_point: Option<u64>) -> Self {
        Self {
            entry_point: default_entry_point.unwrap_or(0x0),
            pc: default_entry_point.unwrap_or(0x0),
            labels: Default::default(),
            label_refs: Default::default(),
            datas: Default::default(),
            data_refs: Default::default(),
            header: Default::default(),
            includes: Default::default(),
            output: Default::default(),
            current_line: 0,
            input_lines: input.trim().lines(),
        }
    }

    fn header_line(
        &mut self,
        line: &str,
        existing_includes: &HashMap<String, String>,
    ) -> Result<(), Box<dyn Error>> {
        let mut spl = line[1..].split_whitespace();
        match spl.next() {
            Some("ent") => {
                if let Some(spl1) = spl.next() {
                    if &spl1[..2] == "0x" {
                        self.entry_point = u64::from_str_radix(&spl1[2..], 16)?;
                        self.pc = self.entry_point;
                    } else {
                        self.entry_point = spl1.parse::<u64>()?;
                        self.pc = self.entry_point;
                    }
                } else {
                    return Err(AssemblyError(format!("Invalid `ent` header tag")).into());
                }
                Ok(())
            }
            Some("include") => {
                if let Some(first_token) = spl.next() {
                    let filename = &line[line.find(first_token).unwrap()..];
                    let filename = filename.strip_prefix('"').unwrap_or(filename);
                    let filename = filename.strip_suffix('"').unwrap_or(filename);
                    if !self.includes.contains_key(&filename.to_owned())
                        && !existing_includes.contains_key(&filename.to_owned())
                    {
                        let mut file = File::open(filename)?;
                        let mut buf = String::new();
                        file.read_to_string(&mut buf)?;
                        self.includes.insert(filename.to_owned(), buf);
                    }
                    // println!("Included {filename}.");
                }
                Ok(())
            }
            Some(tag) => Err(AssemblyError(format!("Unknown header tag: {tag}")).into()),
            _ => todo!(),
        }
    }

    fn assemble_includes(
        &mut self,
        existing_includes: &HashMap<String, String>,
        existing_labels: &HashMap<String, u64>,
        existing_datas: &HashMap<String, Data>,
    ) -> Result<(), Box<dyn Error>> {
        for (filename, asm) in self.includes.iter() {
            let mut assembler = Assembler::new(asm, Some(self.pc));
            // println!("Assembling included file {filename}.");
            let includes = self
                .includes
                .iter()
                .chain(existing_includes.iter())
                .map(|(k, v)| (k.to_owned(), v.to_owned()))
                .collect();
            let datas = self
                .datas
                .iter()
                .chain(existing_datas.iter())
                .map(|(k, v)| (k.to_owned(), v.to_owned()))
                .collect();
            let labels = self
                .labels
                .iter()
                .chain(existing_labels.iter())
                .map(|(k, v)| (k.to_owned(), v.to_owned()))
                .collect();

            let assembled = assembler
                .assemble_impl(false, false, &includes, &labels, &datas)
                .map_err(|err| {
                    println!("Error while parsing included file: {filename}");
                    err
                })?;
            // self.labels = labels;
            // self.datas = datas;
            for (label, loc) in assembler.labels {
                if self.labels.get(&label).is_some() {
                    // return Err(AssemblyError(format!("Error including {filename}: duplicate label `{label}`")).into())
                    println!("Warning: Found duplicate of label {label} in {filename}, ignoring it")
                }
                self.labels.insert(label, loc);
            }
            for (label, refs) in assembler.label_refs {
                if let Some(old) = self.label_refs.insert(label.clone(), refs.clone()) {
                    self.label_refs
                        .get_mut(&label)
                        .unwrap()
                        .extend_from_slice(&refs);
                    self.label_refs
                        .get_mut(&label)
                        .unwrap()
                        .extend_from_slice(&old);
                }
            }
            for (data_name, data) in assembler.datas {
                if self.datas.get(&data_name).is_some() {
                    // return Err(AssemblyError(format!("Error including {filename}: duplicate data `{data_name}`")).into())
                    println!(
                        "Warning: Found duplicate of data {data_name} in {filename}, ignoring it"
                    )
                }
                self.datas.insert(data_name.clone(), data);
            }
            for (data_name, refs) in assembler.data_refs {
                if let Some(old) = self.data_refs.insert(data_name.clone(), refs.clone()) {
                    self.data_refs
                        .get_mut(&data_name)
                        .unwrap()
                        .extend_from_slice(&refs);
                    self.data_refs
                        .get_mut(&data_name)
                        .unwrap()
                        .extend_from_slice(&old);
                }
            }

            self.output.extend_from_slice(&assembled);
            self.pc += assembled.len() as u64;
        }
        Ok(())
    }

    fn data_line(&mut self, line: &str) -> Result<(), Box<dyn Error>> {
        let mut spl = line.split_whitespace();
        let data_name = spl
            .next()
            .ok_or(AssemblyError(format!("Expected token after `@`")))?;
        let first_token = spl
            .next()
            .ok_or(AssemblyError(format!("Expected multiple tokens after `@`")))?;
        if first_token.starts_with('\"') && line.ends_with('\"') {
            let data = &line[line.find(first_token).unwrap()..];
            let data = data.strip_prefix('"').unwrap_or(data);
            let data = data.strip_suffix('"').unwrap_or(data);
            if !data.is_ascii() {
                return Err(AssemblyError(format!(
                    "Only ASCII encoded data strings are supported"
                ))
                .into());
            }
            let mut data = data.to_owned();
            data.push('\0');
            let data_len = data.len();
            if self
                .datas
                .insert(
                    data_name.to_owned(),
                    Data {
                        loc: self.pc,
                        data: data.into_bytes().into_iter().collect::<Vec<_>>(),
                    },
                )
                .is_some()
            {
                return Err(AssemblyError(format!("Found duplicate data tag: {data_name}")).into());
            }
            self.pc += data_len as u64;
            self.output.extend_from_slice(&vec![0u8; data_len]);
        } else {
            match first_token {
                "resb" => {
                    let amount = spl
                        .next()
                        .ok_or(AssemblyError(format!("Expected value after `resb`")))?;
                    let amount = if let Some(stripped) = amount.strip_prefix("0x") {
                        usize::from_str_radix(stripped, 16)?
                    } else {
                        amount.parse::<usize>()?
                    };
                    // println!("Reserving {amount} bytes at {:#x}.", self.pc);
                    if self
                        .datas
                        .insert(
                            data_name.to_owned(),
                            Data {
                                loc: self.pc,
                                data: vec![0u8; amount],
                            },
                        )
                        .is_some()
                    {
                        return Err(AssemblyError(format!(
                            "Found duplicate data tag: {data_name}"
                        ))
                        .into());
                    }
                    self.pc += amount as u64;
                    self.output.extend_from_slice(&vec![0u8; amount]);
                }
                literal if literal.starts_with('$') => {
                    let val = &literal[1..];
                    let val = if let Some(stripped) = val.strip_prefix("0x") {
                        u64::from_str_radix(stripped, 16)?
                    } else {
                        val.parse::<u64>()?
                    };
                    if self
                        .datas
                        .insert(
                            data_name.to_owned(),
                            Data {
                                loc: self.pc,
                                data: val.to_le_bytes().to_vec(),
                            },
                        )
                        .is_some()
                    {
                        return Err(AssemblyError(format!(
                            "Found duplicate data tag: {data_name}"
                        ))
                        .into());
                    }
                    self.pc += size_of::<u64>() as u64;
                    self.output.extend_from_slice(&vec![0u8; size_of::<u64>()]);
                }
                tag => return Err(AssemblyError(format!("Unsupported data tag: {tag}")).into()),
            }
        }
        Ok(())
    }

    fn parse_line(
        &mut self,
        line: &str,
        op_variants: &HashMap<InstructionVariant, [u8; 3]>,
        regs: &HashMap<&'static str, u8>,
    ) -> Result<(), Box<dyn Error>> {
        let spl = line.split_ascii_whitespace().collect::<Vec<_>>();
        let first_semicolon = spl
            .iter()
            .enumerate()
            .find(|s| s.1.contains(';'))
            .map(|s| s.0)
            .unwrap_or(spl.len());
        let spl = spl[..first_semicolon].to_vec();
        let mut found = None;
        'outer: for (opt, bytecode) in op_variants.iter() {
            match opt.parse(line) {
                Ok(_) => {
                    self.output.extend_from_slice(bytecode);
                    found = Some(opt);
                    break 'outer;
                }
                Err(_e) => {
                    // println!("{:?} didn't work", opt);
                }
            }
        }
        if let Some(_found) = found {
            // println!("Found match for line: {line} ===> {}", found.basic_str_rep());
        } else {
            return Err(AssemblyError(format!("Couldn't find match for line: {line}")).into());
        }
        let mut n = found.unwrap().n_args as u64 + 3; // +1 for the metadata byte
        for arg in &spl[1..] {
            // check if it's an offset calculation
            // println!("{} ", arg);
            if tuple((
                nom::bytes::complete::tag("["),
                offset,
                nom::bytes::complete::tag("]"),
            ))(arg)
            .is_ok()
            {
                // println!("is an offset calculation");
                let plus = arg.find('+').unwrap();
                let offset = &arg[..plus];
                let offset = offset.strip_prefix('[').unwrap_or(offset);
                let register = &arg[plus + 1..arg.len()];
                let register = register.strip_suffix(']').unwrap_or(register);
                let offset = offset.parse::<isize>()?;
                let register = regs[register];
                self.output.push(OFFSET);
                self.output.extend_from_slice(&offset.to_le_bytes());
                self.output.push(register);
                n += 9; // because we have an offset (literal sized) AND a register
            } else if ["b", "w", "d", "q"].contains(arg) {
                continue;
            } else {
                let arg = arg.strip_prefix('[').unwrap_or(arg);
                let arg = arg.strip_suffix(']').unwrap_or(arg);
                if regs.contains_key(arg) {
                    // println!("is a register");
                    self.output.push(regs[arg]);
                } else if let Some(arg) = arg.strip_prefix('$') {
                    // println!("is a literal number");
                    let arg = if let Some(arg) = arg.strip_prefix("0x") {
                        u64::from_str_radix(arg, 16)?
                    } else {
                        arg.parse::<u64>()?
                    };

                    self.output.push(LIT);
                    self.output.extend_from_slice(&arg.to_le_bytes());
                    n += 8;
                } else if arg.starts_with('%') {
                    // println!("is a label");
                    if let Some(val) = self.label_refs.get_mut(arg) {
                        val.push(self.pc + n);
                    } else {
                        self.label_refs.insert(arg.to_string(), vec![self.pc + n]);
                    }
                    self.output.push(LIT);
                    self.output.extend_from_slice(&[0; 8]);
                    n += 8;
                } else if arg.starts_with('@') {
                    // println!("is a data");
                    if let Some(val) = self.data_refs.get_mut(arg) {
                        val.push(self.pc + n);
                    } else {
                        self.data_refs.insert(arg.to_string(), vec![self.pc + n]);
                    }
                    self.output.push(LIT);
                    self.output.extend_from_slice(&[0; 8]);
                    n += 8;
                } else {
                    return Err(AssemblyError(format!("Error parsing arg: {arg}")).into());
                }
            }
        }
        self.pc += n;
        Ok(())
    }

    pub fn assemble(&mut self) -> Result<Vec<u8>, Box<dyn Error>> {
        self.assemble_impl(
            true,
            true,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
        )
    }

    fn assemble_impl(
        &mut self,
        include_header: bool,
        resolve_symbols: bool,
        existing_includes: &HashMap<String, String>,
        existing_labels: &HashMap<String, u64>,
        existing_datas: &HashMap<String, Data>,
    ) -> Result<Vec<u8>, Box<dyn Error>> {
        let bytecodes = gen_bytecodes();
        let regs = gen_regs();
        self.header.extend_from_slice(HEADER_MAGIC);
        let mut in_header = true;
        for (i, line) in self.input_lines.clone().enumerate() {
            self.current_line = i;
            let line = line.trim();
            if line.is_empty() {
                continue;
            }

            if line.starts_with(';') {
                continue;
            } else if line.starts_with('!') {
                if in_header {
                    self.header_line(line, existing_includes)?;
                } else {
                    return Err(AssemblyError(format!(
                        "Found header line outside the header: {line}"
                    ))
                    .into());
                }
            } else if line.starts_with('@') {
                in_header = false;
                // println!("Detected data {} at pc={:#x}", line, self.pc);
                self.data_line(line)?;
            } else if line.starts_with('%') {
                in_header = false;
                // println!("Detected label {} at pc={:#x}", line, self.pc);
                if self.labels.insert(line.into(), self.pc).is_some() {
                    return Err(AssemblyError(format!("Found duplicate label: {line}")).into());
                }
            } else {
                in_header = false;
                self.parse_line(line, &bytecodes, &regs)?;
            }
        }

        self.assemble_includes(existing_includes, existing_labels, existing_datas)?;

        if resolve_symbols {
            for (label, refs) in &self.label_refs {
                for reference in refs {
                    let label_value = self
                        .labels
                        .get(label)
                        .or(existing_labels.get(label))
                        .ok_or(AssemblyError(format!(
                            "Undefined reference to label {label}"
                        )))?;
                    // println!("Inserting addr of label {label} ({label_value:#x}) referenced at {reference:#x}.");
                    for (i, b) in label_value.to_le_bytes().iter().enumerate() {
                        self.output[(*reference) as usize - self.entry_point as usize + i] = *b;
                    }
                }
            }
            for data in self.datas.values() {
                let loc = data.loc;
                let data = &data.data;
                // let data_len = data.len();
                // println!("Inserting data {data_name} located at {loc:#x} (size {data_len}).");
                for (i, b) in data.iter().enumerate() {
                    self.output[loc as usize - self.entry_point as usize + i] = *b;
                }
            }
            for (data_name, refs) in &self.data_refs {
                for reference in refs {
                    let loc = self
                        .datas
                        .get(data_name)
                        .or(existing_datas.get(data_name))
                        .ok_or(AssemblyError(format!(
                            "Undefined reference to data {data_name}"
                        )))?
                        .loc;
                    // println!("Inserting addr of data {data_name} ({loc:#x}) referenced at {reference:#x}.");
                    for (i, b) in loc.to_le_bytes().iter().enumerate() {
                        self.output[(*reference) as usize - self.entry_point as usize + i] = *b;
                    }
                }
            }
        }

        self.header.extend_from_slice(HEADER_ENTRY_POINT);
        self.header
            .extend_from_slice(&self.entry_point.to_le_bytes());
        self.header.extend_from_slice(HEADER_END);
        let mut out = Vec::new();
        if include_header {
            out.extend_from_slice(&self.header);
        }
        out.extend_from_slice(&self.output);
        self.output = out;
        Ok(self.output.clone())
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = args().collect::<Vec<_>>();
    let mut args = if args.len() < 2 {
        // return Err(AssemblyError("Not enough arguments").into())
        let mut args = vec!["test.k4sm".to_owned()];
        args.extend_from_slice(
            &glob::glob("rusttest/target/x86_64-unknown-linux-musl/release/deps/rusttest*.bc")?
                .map(|path| path.unwrap().into_os_string().into_string().unwrap())
                .collect::<Vec<_>>(),
        );
        // args.extend_from_slice(
        //     &glob::glob("rusttest/target/x86_64-unknown-linux-musl/release/deps/core*.bc")?
        //         .map(|path| path.unwrap().into_os_string().into_string().unwrap())
        //         .collect::<Vec<_>>(),
        // );
        // println!("{:?}", args);
        args
    } else {
        args[1..].to_vec()
    };
    args.sort_by_key(|arg| !arg.ends_with(".bc"));
    for arg in args {
        if arg.ends_with(".bc") {
            // it's a LLVM bitcode file, parse it to k4sm assembly first
            println!("Parsing {} into K4SM assembly.", arg);
            let mut parser = Parser::new(arg.clone());
            
            let asm = parser.emit_k4sm()?;
            let out_name = PathBuf::from(arg.clone()).file_name().unwrap().to_str().unwrap().to_owned();
            let out_name = out_name.split('-').next().unwrap().to_owned();
            let mut out_name = out_name.strip_suffix(".bc").unwrap_or(&out_name).to_owned();
            out_name.push_str(".k4sm");
            
            let mut file = File::create(out_name.clone())?;
            writeln!(file, "{}", asm)?;
        } else {
            let mut file = File::open(arg.clone())?;
            let mut buf = String::new();
            file.read_to_string(&mut buf)?;
            println!("Assembling {}.", arg);
            let out = Assembler::new(&buf, None).assemble()?;
            let mut out_name = arg.replace(".k4sm", ".k4s");
            if out_name == arg {
                out_name.push_str(".k4s");
            }
            let mut out_file = File::create(out_name)?;
            out_file.write_all(&out)?;
            println!("Wrote {} bytes.", out.len());
        }
    }
    Ok(())
}
