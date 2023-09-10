This is Bad APSqRt, a bad square root algorithm for use with [rustc\_apfloat](https://crates.io/crates/rustc_apfloat). 

(APFloat is short for Arbitrary Precision Floating Point. Bad APSqRt is short for Bad Algorithm for Square Roots with APFloat. Unlike APFloat, it is only designed to work with IEEE 754 single-, double-, and quad-precision floats; thus, it does not provide arbitrary precision itself.)

# Why

rustc\_apfloat is a software floating point library. It's a Rust conversion of "APFloat" from the LLVM project. These libraries emphasize clarity and correctness over speed. They're used, respectively, in the `rustc` and `clang` compilers to do compile-time calculation of floating point operations. These compilers don't use the host's floating point because, when cross compiling, host and target behavior may be difficult or impossible to reconcile. Emulators often have the same problem. I was writing a deterministic RV32-G emulator, and as part of that, I needed to emulate the RISC-V standard's floating point specifications specifically. rustc\_apfloat to the rescue!

Because rustc\_apfloat implements almost every operation needed for RISC-V floating point emulation, it made my life a lot easier—but that last operation, square root, is important, so I had to implement it myself. It would have been faster and easier to use the host's `sqrt` functions for these, and to accept the inconsistencies in emulation, but my emulator is meant to fit in a multiplayer game's logic loop (?!!?!) so it *has* to be deterministic. A bad algorithm that is wrong in exactly the same ways on any platform is, therefore, better than a good algorithm that has even the slightest disagreement between platforms.

# Algorithm

This crate implements a very unsophisticated, but simple to understand, algorithm. It uses a sort of binary search to *very slowly* refine an initial, terrible estimate of the square root, using only integer addition/subtraction and floating point multiplication. I implemented this algorithm because Newton-Raphson went over my head. If you don't like my algorithm, or find one ULP of error to be unacceptable, I would seriously love it if you would [get in contact with me](mailto:solra@bizna.name) and help me understand a better algorithm (like Newton-Raphson).

# Accuracy

If there is an exact solution, Bad APSqRt always finds it. 75% of inexact solutions will be correctly rounded, 25% will be off by a single ULP—the least significant bit will be wrong but all other bits will be right. (If I made full use of the AP part of the APFloat library, I could reduce the error to zero—but math is hard and I am dumb.) All NaNs it produces are "canon NaNs" according to the RISC-V standard.

# Legalese

Bad APSqRt is copyright 2023 Solra Bizna.

Bad APSqRt is licensed under the Apache 2 with LLVM exception license. This is the same license as the rustc\_apfloat crate. This is the simplest way to guarantee that Bad APSqRt can be used anywhere anywhere rustc\_apfloat can.
