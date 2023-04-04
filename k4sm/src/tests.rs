// #[test]
// fn test_op_size() {
//     let ops = gen_bytecodes();
//     let regs = gen_regs();
//     let variant = OpVariant {
//         mnemonic: "mov".into(),
//         op_args: k4s::OpArgs::ValVal,
//         n_args: 2,
//         metadata: MetadataByte::new(k4s::OpSize::Qword),
//     };
//     assert!(variant.parse("mov q ra rb").is_ok());
//     let out = Assembler::new("mov q ra rb", None).assemble().unwrap();

//     let bytes = ops[&variant];
//     assert_eq!(out[out.len() - 4..], vec![bytes[0], bytes[1], regs["ra"], regs["rb"]]);
// }
