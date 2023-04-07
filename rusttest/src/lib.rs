#![no_std]
#![no_main]
#![feature(type_ascription)]
#![allow(clippy::not_unsafe_ptr_arg_deref)]

#[cfg(not(test))]
use core::panic::PanicInfo;

#[cfg(not(test))]
#[panic_handler]
pub extern "C" fn panic_handler(_: &PanicInfo) -> ! {
    // unsafe {
    //     printstr("Panic!!!")
    // }
    // println("Panic!!!");
    loop {}
}

pub const MAX_MEM: u64 = 0x100000000;

extern "C" {
    pub fn hlt() -> !;
    pub(crate) fn printi_(rg: u64);
    pub(crate) fn printc_(rg: u8);
    pub fn memcpy(dest: *mut u8, src: *const u8, n_bytes: u64);
}

pub fn printi(val: u64) {
    unsafe { 
        printi_(val)
    }
}

pub fn printc(val: u8) {
    unsafe { 
        printc_(val)
    }
}

#[doc(hidden)]
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn printptrln(s: *const u8, len: usize) {
    let s = core::slice::from_raw_parts(s, len);
    for c in s {
        printc(*c);
    }
    printc(b'\n');
}

pub fn println(s: &str) {
    unsafe {
        printptrln(s.as_bytes().as_ptr(), s.as_bytes().len())
    }
}

#[repr(C, packed)]
pub struct BootInfo {
    pub max_mem: u64,
}

#[no_mangle]
pub extern "C" fn kernel_main(boot_info_addr: *const BootInfo) -> ! {
    printi(boot_info_addr as u64);
    let boot_info = unsafe { &*boot_info_addr };
    printi(boot_info.max_mem);
    println("Hello from the kernel!");
    // panic!();
    unsafe { hlt() }
}
