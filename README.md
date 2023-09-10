This is Bad APSqRt, a bad square root algorithm for use with [rustc\_apfloat](https://crates.io/crates/rustc_apfloat). Please use [IEEE APSqRt](https://github.com/SolraBizna/ieee-apsqrt) instead!

(APFloat is short for Arbitrary Precision Floating Point. Bad APSqRt is short for Bad Algorithm for Square Roots with APFloat. Unlike APFloat, it is only designed to work with IEEE 754 single-, double-, and quad-precision floats; thus, it does not provide arbitrary precision itself.)

# Why

rustc\_apfloat is a software floating point library. It's a Rust conversion of "APFloat" from the LLVM project. These libraries emphasize clarity and correctness over speed. They're used, respectively, in the `rustc` and `clang` compilers to do compile-time calculation of floating point operations. These compilers don't use the host's floating point because, when cross compiling, host and target behavior may be difficult or impossible to reconcile. Emulators often have the same problem. I was writing a deterministic RV32-G emulator, and as part of that, I needed to emulate the RISC-V standard's floating point specifications specifically. rustc\_apfloat to the rescue!

Because rustc\_apfloat implements almost every operation needed for RISC-V floating point emulation, it made my life a lot easier—but that last operation, square root, is important, so I had to implement it myself. It would have been faster and easier to use the host's `sqrt` functions for these, and to accept the inconsistencies in emulation, but my emulator is meant to fit in a multiplayer game's logic loop (?!!?!) so it *has* to be deterministic. A bad algorithm that is wrong in exactly the same ways on any platform is, therefore, better than a good algorithm that has even the slightest disagreement between platforms.

I implemented this naive guess-and-check algorithm first, partly to see if I could. Once I'd implemented and characterized it, I decided to try implementing Newton-Raphson instead. That implementation became the [IEEE APSqRt](https://github.com/SolraBizna/ieee-apsqrt) crate. This crate continues to exist for educational purposes, but otherwise, you should really use IEEE APSqRt instead!

# Algorithm

This crate implements a very unsophisticated, but simple to understand, algorithm. It uses a sort of binary search to *very slowly* refine an initial, terrible estimate of the square root, using only integer addition/subtraction and floating point multiplication.

# Accuracy

If there is an exact solution, either form of Bad APSqRt always finds it. For `bad_sqrt_slow`, 75% of inexact solutions will be correctly rounded, 25% will be off by a single ULP—the least significant bit will be wrong but all other bits will be right. For `bad_sqrt_slower`, it will usually take twice as many iterations, but the answer will be 100% correct. (`bad_sqrt_slower` is, unfortunately, due to limitations of rustc\_apfloat, only available for 32- and 64-bit floats.)

All NaNs produced by Bad APSqRt are "canon NaNs" according to the RISC-V standard.

# How to use

Don't! This algorithm is bad. [IEEE APSqRt](https://github.com/SolraBizna/ieee-apsqrt) is much faster!

# Legalese

Bad APSqRt is copyright 2023 Solra Bizna.

Bad APSqRt is licensed under the Apache 2 with LLVM exception license. This is the same license as the rustc\_apfloat crate. This is the simplest way to guarantee that Bad APSqRt can be used anywhere anywhere rustc\_apfloat can.
