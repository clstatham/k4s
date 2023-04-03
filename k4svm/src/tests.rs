
// #[cfg(test)]
// pub mod instr_tests {
//     use k4s::{gen_bytecodes, OpVariant, MetadataByte, OpArgs, OpSize, Literal, LIT, HEADER_MAGIC, HEADER_ENTRY_POINT, Qword, HEADER_END};
//     use zerocopy::AsBytes;
    
    
    
//     pub fn literal(val: Literal) -> Vec<u8> {
//         let mut bytes = vec![LIT];
//         bytes.extend_from_slice(val.as_qword().as_bytes());
//         bytes
//     }
    
//     pub fn generate_instr(mn: &str, arg_types: OpArgs, size: OpSize, args: &[u8]) -> Vec<u8> {
//         let ops = gen_bytecodes();
//         let variant = OpVariant {
//             mnemonic: mn.into(),
//             op_args: arg_types,
//             n_args: arg_types.n_args(),
//             metadata: MetadataByte::new(size),
//         };
    
//         let mut bytes = ops[&variant].to_vec();
//         bytes.extend_from_slice(args);
//         bytes
//     }

//     pub fn generate_program(data: &[u8]) -> Vec<u8> {
//         let mut out = vec![];
//         out.extend_from_slice(HEADER_MAGIC);
//         out.extend_from_slice(HEADER_ENTRY_POINT);
//         out.extend_from_slice(Qword::new(0x100).as_bytes());
//         out.extend_from_slice(HEADER_END);
//         out.extend_from_slice(data);
//         out.extend_from_slice(&generate_instr("hlt", OpArgs::NoArgs, OpSize::Unsized, &[]));
//         out
//     }

//     #[test]
//     pub fn test_mov_reg_lit() {
//         let regs = gen_regs();
//         let mut args = vec![regs["ra"]];
//         args.extend_from_slice(&literal(Literal::Qword(42.into())));
//         let instr = generate_instr("mov", OpArgs::ValVal, OpSize::Qword, &args);
//         let program = generate_program(&instr);
//         let mut emu = Emulator::new(&program, 0x1000).unwrap();
//         emu.run().unwrap();
//         assert_eq!(emu.regs.ra.get(), 42);
//     }

//     #[test]
//     pub fn test_mov_litadr_lit() {
//         // let regs = gen_regs();
//         let mut args = vec![];
//         args.extend_from_slice(&literal(Literal::Qword(0x200.into())));
//         args.extend_from_slice(&literal(Literal::Qword(42.into())));
//         let instr = generate_instr("mov", OpArgs::AdrVal, OpSize::Qword, &args);
//         let program = generate_program(&instr);
//         let mut emu = Emulator::new(&program, 0x1000).unwrap();
//         emu.run().unwrap();
//         assert_eq!(emu.ram.peek::<Qword>(0x200.into()).get(), 42);
//     }
// }

