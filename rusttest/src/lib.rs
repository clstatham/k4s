#![no_std]
#![feature(type_ascription)]

#[cfg(not(test))]
use core::panic::PanicInfo;

#[cfg(not(test))]
#[panic_handler]
pub extern "C" fn panic_handler(_: &PanicInfo) -> ! {
    // unsafe {
    //     printstr("Panic!!!")
    // }
    loop {}
}

const STATIC_ARRAY: &[u8] = "Hello I'm a STATIC_ARRAY".as_bytes();

extern "C" {
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
pub unsafe extern "C" fn printstr(s: *const u8, len: usize) {
    let s = core::slice::from_raw_parts(s, len);
    for c in s {
        printc(*c);
    }
}

#[no_mangle]
pub extern "C" fn add(left: usize, right: usize) -> usize {
    unsafe {
        printstr(STATIC_ARRAY.as_ptr(), STATIC_ARRAY.len());
    }
    left + right
}
