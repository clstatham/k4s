use std::{env::args, error::Error, fmt::Display, collections::HashMap, str::Lines, mem::size_of, fs::File, io::{Read, Write}};

use regex::RegexSet;
use k4s::*;

#[derive(Debug)]
pub struct AssemblyError(String);
impl Display for AssemblyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl Error for AssemblyError {}

fn gen_matchers() -> RegexSet {
    let match0 = r"^[A-Za-z0-9_]+$";
    let match1 = r"^[A-Za-z0-9_]+\s+[A-Za-z0-9_]+\s+\$?@?[A-Za-z0-9_]+$";
    let match2 = r"^[A-Za-z0-9_]+\s+[A-Za-z0-9_]+\s+\[[A-Za-z0-9_]+\]$";
    let match3 = r"^[A-Za-z0-9_]+\s+\[?[A-Za-z0-9_]+\]\s+\$?[A-Za-z0-9_]+$";
    let match4 = r"^[A-Za-z0-9_]+\s+\[?[A-Za-z0-9_]+\]\s+\[\$?[A-Za-z0-9_]+\]$";
    let match5 = r"^[A-Za-z0-9_]+\s+\$?%?@?[A-Za-z0-9_]+$";
    let match6 = r"^[A-Za-z0-9_]+\s+\[?[A-Za-z0-9_]+\]$";
    RegexSet::new(&[
        match0,
        match1,
        match2,
        match3,
        match4,
        match5,
        match6,
    ]).unwrap()
}

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
    pub fn new(input: &'a String, default_entry_point: Option<u64>) -> Self {
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

    fn header_line(&mut self, line: &str) -> Result<(), Box<dyn Error>> {
        let mut spl = line[1..].split_whitespace();
        match spl.next() {
            Some("ent") => {
                if let Some(spl1) = spl.next() {
                    if &spl1[..2] == "0x" {
                        self.entry_point = u64::from_str_radix(&spl1[2..], 16)?;
                        self.pc = self.entry_point;
                    } else {
                        self.entry_point = u64::from_str_radix(spl1, 10)?;
                        self.pc = self.entry_point;
                    }
                } else {
                    return Err(AssemblyError(format!("Invalid `ent` header tag")).into())
                }
                Ok(())
            }
            Some("include") => {
                if let Some(first_token) = spl.next() {
                    let filename = &line[line.find(first_token).unwrap()..];
                    let filename = filename.strip_prefix('"').unwrap_or(filename);
                    let filename = filename.strip_suffix('"').unwrap_or(filename);
                    let mut file = File::open(filename)?;
                    let mut buf = String::new();
                    file.read_to_string(&mut buf)?;
                    self.includes.insert(filename.to_owned(), buf);
                    println!("Included {filename}.");
                }
                Ok(())
            }
            Some(tag) => Err(AssemblyError(format!("Unknown header tag: {tag}"), ).into()),
            _ => todo!()
        }
    }

    fn assemble_includes(&mut self) -> Result<(), Box<dyn Error>> {
        for (filename, asm) in self.includes.iter() {
            let mut assembler = Assembler::new(asm, Some(self.pc));
            println!("Assembling included file {filename}.");
            let assembled = assembler.assemble(false).map_err(|err| {
                println!("Error while parsing included file: {filename}");
                err
            })?;
            for (label, loc) in assembler.labels {
                if let Some(_) = self.labels.insert(label.clone(), loc) {
                    return Err(AssemblyError(format!("Error including {filename}: duplicate label `{label}`")).into())
                }
            }
            // for (label, refs) in assembler.label_refs {
            //     if let Some(_) = self.label_refs.insert(label.clone(), refs.clone()) {
            //         self.label_refs.get_mut(&label).unwrap().extend_from_slice(&refs);
            //     }
            // }
            for (data_name, data) in assembler.datas {
                if let Some(_) = self.datas.insert(data_name.clone(), data) {
                    return Err(AssemblyError(format!("Error including {filename}: duplicate data `{data_name}`")).into())
                }
            }
            // for (data_name, refs) in assembler.data_refs {
            //     if let Some(_) = self.data_refs.insert(data_name.clone(), refs.clone()) {
            //         self.data_refs.get_mut(&data_name).unwrap().extend_from_slice(&refs);
            //     }
            // }
            
            self.output.extend_from_slice(&assembled);
            self.pc += assembled.len() as u64;
        }
        Ok(())
    }

    fn data_line(&mut self, line: &str) -> Result<(), Box<dyn Error>> {
        let mut spl = line.split_whitespace();
        let data_name = spl.next().ok_or(AssemblyError(format!("Expected token after `@`")))?;
        let first_token = spl.next().ok_or(AssemblyError(format!("Expected multiple tokens after `@`")))?;
        if first_token.starts_with("\"") && line.ends_with("\"") {
            let data = &line[line.find(first_token).unwrap()..];
            let data = data.strip_prefix('"').unwrap_or(data);
            let data = data.strip_suffix('"').unwrap_or(data);
            if !data.is_ascii() {
                return Err(AssemblyError(format!("Only ASCII encoded data strings are supported")).into())
            }
            let mut data = data.to_owned();
            data.push('\0');
            let data_len = data.len();
            if let Some(_) = self.datas.insert(data_name.to_owned(), Data { loc: self.pc, data: data.into_bytes().into_iter().collect::<Vec<_>>() }) {
                return Err(AssemblyError(format!("Found duplicate data tag: {data_name}")).into())
            }
            self.pc += data_len as u64;
            self.output.extend_from_slice(&vec![0u8; data_len]);
        } else {
            match first_token {
                "resb" => {
                    let amount = spl.next().ok_or(AssemblyError(format!("Expected value after `resb`")))?;
                    let amount = if amount.starts_with("0x") {
                        usize::from_str_radix(&amount[2..], 16)?
                    } else {
                        usize::from_str_radix(amount, 10)?
                    };
                    println!("Reserving {amount} bytes at {:#x}.", self.pc);
                    if let Some(_) = self.datas.insert(data_name.to_owned(), Data { loc: self.pc, data: vec![0u8; amount] }) {
                        return Err(AssemblyError(format!("Found duplicate data tag: {data_name}")).into())
                    }
                    self.pc += amount as u64;
                    self.output.extend_from_slice(&vec![0u8; amount]);
                }
                literal if literal.starts_with("$") => {
                    let val = &literal[1..];
                    let val = if val.starts_with("0x") {
                        u64::from_str_radix(&val[2..], 16)?
                    } else {
                        u64::from_str_radix(val, 10)?
                    };
                    if let Some(_) = self.datas.insert(data_name.to_owned(), Data { loc: self.pc, data: val.to_le_bytes().to_vec() }) {
                        return Err(AssemblyError(format!("Found duplicate data tag: {data_name}")).into())
                    }
                    self.pc += size_of::<u64>() as u64;
                    self.output.extend_from_slice(&vec![0u8; size_of::<u64>()]);
                }
                tag => return Err(AssemblyError(format!("Unsupported data tag: {tag}")).into())
            }
        }
        Ok(())
    }

    fn parse_line(&mut self, line: &str, matchers: &RegexSet, bytecodes: &HashMap<String, u8>, regs: &HashMap<&'static str, u8>) -> Result<(), Box<dyn Error>> {
        let spl = line.split_whitespace().collect::<Vec<_>>();
        let first_semicolon = spl.iter().enumerate().find(|s| s.1.contains(";")).map(|s| s.0).unwrap_or(spl.len());
        let spl = spl[..first_semicolon].to_vec();
        let mut found = false;
        for (opt, bytecode) in bytecodes.iter() {
            if opt.split_whitespace().next().unwrap() == spl[0] {
                let opt_matches = matchers.matches(&opt);
                let line_matches = matchers.matches(&spl.join(" "));
                if opt_matches.iter().zip(line_matches.iter()).any(|(a, b)| a == b) {
                    self.output.push(*bytecode);
                    found = true;
                    break;
                }
            }
        }
        if !found {
            return Err(AssemblyError(format!("Couldn't find match for line: {line}")).into())
        }
        let mut n = spl.len() as u64;
        for arg in &spl[1..] {
            let arg = arg.strip_prefix("[").unwrap_or(arg);
            let arg = arg.strip_suffix("]").unwrap_or(arg);
            if regs.contains_key(arg) {
                self.output.push(regs[arg]);
            } else if arg.starts_with("$") {
                let arg = &arg[1..];
                let arg = if arg.starts_with("0x") {
                    u64::from_str_radix(&arg[2..], 16)?
                } else {
                    u64::from_str_radix(arg, 10)?
                };
                self.output.push(LIT);
                self.output.extend_from_slice(&arg.to_le_bytes());
                n += 8;
            } else if arg.starts_with("%") {
                if let Some(val) = self.label_refs.get_mut(arg) {
                    val.push(self.pc + n);
                } else {
                    self.label_refs.insert(arg.to_owned(), vec![self.pc + n]);
                }
                self.output.push(LIT);
                self.output.extend_from_slice(&[0; 8]);
                n += 8;
            } else if arg.starts_with("@") {
                if let Some(val) = self.data_refs.get_mut(arg) {
                    val.push(self.pc + n);
                } else {
                    self.data_refs.insert(arg.to_owned(), vec![self.pc + n]);
                }
                self.output.push(LIT);
                self.output.extend_from_slice(&[0; 8]);
                n += 8;
            } else {
                return Err(AssemblyError(format!("Error parsing line: {line}")).into())
            }
        }
        self.pc += n as u64;
        Ok(())
    }

    pub fn assemble(&mut self, include_header: bool) -> Result<Vec<u8>, Box<dyn Error>> {
        let matchers = gen_matchers();
        let bytecodes = gen_bytecodes();
        let regs = gen_regs();
        if include_header {
            self.header.extend_from_slice(HEADER_MAGIC);
        }
        let mut in_header = true;
        for (i, line) in self.input_lines.clone().enumerate() {
            self.current_line = i;
            let line = line.trim();
            if line.is_empty() {
                continue;
            }

            if line.starts_with(";") {
                continue;
            } else if line.starts_with("!") {
                if in_header {
                    self.header_line(line)?;
                } else {
                    return Err(AssemblyError(format!("Found header line outside the header: {line}")).into())
                }
            } else if line.starts_with("@") {
                in_header = false;
                println!("Detected data {} at pc={:#x}", line, self.pc);
                self.data_line(line)?;
            } else if line.starts_with("%") {
                in_header = false;
                println!("Detected label {} at pc={:#x}", line, self.pc);
                if let Some(_) = self.labels.insert(line.into(), self.pc) {
                    return Err(AssemblyError(format!("Found duplicate label: {line}")).into())
                }
            } else {
                in_header = false;
                self.parse_line(line, &matchers, &bytecodes, &regs)?;
            }
        }

        self.assemble_includes()?;

        for (label, refs) in &self.label_refs {
            for reference in refs {
                let label_value = self.labels.get(label).unwrap();
                println!("Inserting addr of label {label} ({label_value:#x}) referenced at {reference:#x}.");
                for (i, b) in label_value.to_le_bytes().iter().enumerate() {
                    self.output[(*reference) as usize - self.entry_point as usize + i] = *b;
                }
            }
        }
        for (data_name, data) in &self.datas {
            let loc = data.loc;
            let data = &data.data;
            let data_len = data.len();
            println!("Inserting data {data_name} located at {loc:#x} (size {data_len}).");
            for (i, b) in data.iter().enumerate() {
                self.output[loc as usize - self.entry_point as usize + i] = *b;
            }
        }
        for (data_name, refs) in &self.data_refs {
            for reference in refs {
                let loc = self.datas[data_name].loc;
                println!("Inserting addr of data {data_name} ({loc:#x}) referenced at {reference:#x}.");
                for (i, b) in loc.to_le_bytes().iter().enumerate() {
                    self.output[(*reference) as usize - self.entry_point as usize + i] = *b;
                }
            }
        }

        self.header.extend_from_slice(HEADER_ENTRY_POINT);
        self.header.extend_from_slice(&self.entry_point.to_le_bytes());
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
    let args = if args.len() < 2 {
        // return Err(AssemblyError("Not enough arguments").into())
        vec!["test.k4sm".to_owned()]
    } else {
        args[1..].to_vec()
    };
    for arg in args {
        let mut file = File::open(arg.clone())?;
        let mut buf = String::new();
        file.read_to_string(&mut buf)?;
        let out = Assembler::new(&buf, None).assemble(true)?;
        let mut out_name = arg.replace(".k4sm", ".k4s");
        if out_name == arg {
            out_name.extend(".k4s".chars());
        }
        let mut out_file = File::create(out_name)?;
        out_file.write_all(&out)?;
        println!("Wrote {} bytes.", out.len());
    }
    Ok(())
}
