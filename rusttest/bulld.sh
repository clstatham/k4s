#!/bin/bash

set -e

cargo clean
RUSTFLAGS="--emit=llvm-bc,llvm-ir" cargo build --release