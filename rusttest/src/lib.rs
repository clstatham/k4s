#![no_std]

#[cfg(not(test))]
use core::panic::PanicInfo;

#[cfg(not(test))]
#[panic_handler]
pub extern "C" fn panic_handler(_: &PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn add(left: usize, right: usize) -> usize {
    left + right
}
