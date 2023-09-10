use std::cmp::Ordering;

use rustc_apfloat::{
    Float, Round, StatusAnd, Status,
    ieee::{Semantics, Single, SingleS, Double, DoubleS, Quad, QuadS, IeeeFloat}};

mod privacy_hack {
    use super::*;
    use std::{
        fmt::Debug,
        ops::{Add, AddAssign, BitAnd, BitOr, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign},
    };
    pub trait InnerFloatRepr {
        type Bits : 
            Copy + Debug + Eq + Ord
            + Add<Output=Self::Bits>
            + AddAssign<Self::Bits>
            + Sub<Output=Self::Bits>
            + SubAssign<Self::Bits>
            + Shr<i32, Output=Self::Bits>
            + ShrAssign<i32>
            + Shl<i32, Output=Self::Bits>
            + ShlAssign<i32>
            + Not<Output=Self::Bits>
            + BitOr<Self::Bits, Output=Self::Bits>
            + BitAnd<Self::Bits, Output=Self::Bits>
            + Into<u128>
            + TryFrom<u128>
            + From<u16>;
        const ZERO: Self::Bits;
        const ONE: Self::Bits;
        const EXPONENT_BIAS: i16 = Self::Semantics::MAX_EXP as i16;
        const MAX_EXPONENT: i16 = Self::Semantics::MAX_EXP as i16;
        const IMPLIED_ONE: Self::Bits;
        type Float: rustc_apfloat::Float + Debug;
        type Semantics: rustc_apfloat::ieee::Semantics;
        fn ilog2(bits: &Self::Bits) -> u16;
        fn get_exponent(bits: &Self::Bits) -> i16 {
            (*bits >> ((Self::Semantics::PRECISION-1) as i32))
                .into() as i16 - Self::EXPONENT_BIAS
        }
        // these only work if we don't borrow/carry through the sign bit...
        // we will only be calling these on numbers that have plenty of
        // room above and below, so we should be fine.
        fn add_exponent(bits: &mut Self::Bits, value: u16) {
            *bits += Self::Bits::from(value) << (Self::Semantics::PRECISION-1) as i32
        }
        fn subtract_exponent(bits: &mut Self::Bits, value: u16) {
            *bits -= Self::Bits::from(value) << (Self::Semantics::PRECISION-1) as i32
        }
        fn get_significand(bits: &Self::Bits) -> Self::Bits {
            if Self::get_exponent(bits) == -Self::EXPONENT_BIAS {
                // subnormal number
                (*bits & (Self::IMPLIED_ONE-Self::ONE)) << 1
                // (shift left by 1 to compensate for the wrong exponent being
                // returned)
            } else {
                *bits & (Self::IMPLIED_ONE-Self::ONE) | Self::IMPLIED_ONE
            }
        }
        fn from_exponent_and_significand(mut exponent: i16, mut significand: Self::Bits) -> Self::Bits {
            // this implementation doesn't work for subnormal numbers, but we
            // never generate a subnormal square root 
            while significand >= Self::IMPLIED_ONE << 1 {
                significand >>= 1;
                exponent += 1;
            }
            while significand <= Self::IMPLIED_ONE >> 1 {
                significand <<= 1;
                exponent -= 1;
            }
            if exponent <= -Self::EXPONENT_BIAS {
                // subnormal result
                while exponent <= -Self::EXPONENT_BIAS {
                    exponent += 1;
                    significand >>= 1;
                }
                significand
            } else {
                // normal result
                assert!(exponent <= Self::MAX_EXPONENT, "overflow! overflow!");
                (significand & !Self::IMPLIED_ONE) | (Self::Bits::from((exponent + Self::EXPONENT_BIAS) as u16) << (Self::Semantics::PRECISION-1) as i32)
            }
        }
    }
    pub trait FloatRepr : InnerFloatRepr {
        const MAX: Self::Bits;
        /// The NaN bit value mandated by the RISC-V specification
        const CANON_NAN: Self::Bits;
        const INFINITY: Self::Bits;
    }
    pub trait WidenableFloatRepr : FloatRepr {
        type WidenedRepr: InnerFloatRepr;
        const EXTRA_PRECISION: u16 = (<Self::WidenedRepr as InnerFloatRepr>::Semantics::PRECISION - Self::Semantics::PRECISION) as u16;
        const EXTRA_MASK: <Self::WidenedRepr as InnerFloatRepr>::Bits;
        const EXTRA_TIE: <Self::WidenedRepr as InnerFloatRepr>::Bits;
        fn widen(bits: Self::Bits) -> <Self::WidenedRepr as InnerFloatRepr>::Bits {
            let exponent = Self::get_exponent(&bits);
            let significand = Self::get_significand(&bits);
            Self::WidenedRepr::from_exponent_and_significand(exponent, <Self::WidenedRepr as InnerFloatRepr>::Bits::try_from((significand.into() as u128) << Self::EXTRA_PRECISION as i32).unwrap_or_else(|_| unreachable!()))
        }
        fn narrow(bits: StatusAnd<<Self::WidenedRepr as InnerFloatRepr>::Bits>, round_mode: Round) -> StatusAnd<Self::Bits> {
            // This function assumes heavily that over- and underflow will not
            // occur. We can do this, since the range of representable square
            // roots is much narrower than the range of representable squares.
            let exponent = Self::WidenedRepr::get_exponent(&bits.value);
            let significand = Self::WidenedRepr::get_significand(&bits.value);
            let high_bits = significand >> Self::EXTRA_PRECISION as i32;
            let low_bits = significand & Self::EXTRA_MASK;
            let mut status = bits.status;
            if low_bits != Self::WidenedRepr::ZERO {
                status |= Status::INEXACT;
            }
            let high_bits = match round_mode {
                Round::TowardNegative | Round::TowardZero => high_bits,
                Round::TowardPositive => {
                    if low_bits != Self::WidenedRepr::ZERO { high_bits + Self::WidenedRepr::ONE }
                    else { high_bits }
                },
                Round::NearestTiesToAway => {
                    match low_bits.cmp(&Self::EXTRA_TIE) {
                        Ordering::Less => high_bits,
                        Ordering::Equal | Ordering::Greater => high_bits + Self::WidenedRepr::ONE,
                    }
                },
                Round::NearestTiesToEven => {
                    match low_bits.cmp(&Self::EXTRA_TIE) {
                        Ordering::Less => high_bits,
                        Ordering::Greater => high_bits + Self::WidenedRepr::ONE,
                        Ordering::Equal => {
                            if low_bits & Self::WidenedRepr::ONE == Self::WidenedRepr::ZERO {
                                high_bits
                            } else {
                                high_bits + Self::WidenedRepr::ONE
                            }
                        },
                    }
                },
            };
            let high_bits = Self::Bits::try_from(high_bits.into() as u128).unwrap_or_else(|_| unreachable!());
            // note: from_exponent_and_significand handles over- and underflow
            // of the significand for us
            let value = Self::from_exponent_and_significand(exponent, high_bits);
            StatusAnd {
                status, value
            }
        }
    }
    pub struct Ieee128;
    impl InnerFloatRepr for Ieee128 {
        type Bits = u128;
        const ZERO: Self::Bits = 0;
        const ONE: Self::Bits = 1;
        const IMPLIED_ONE: Self::Bits = Self::ONE << ((Self::Semantics::PRECISION-1) as i32);
        fn ilog2(bits: &Self::Bits) -> u16 { bits.ilog2() as u16 }
        type Float = Quad;
        type Semantics = QuadS;
    }
    impl FloatRepr for Ieee128 {
        const MAX: Self::Bits = u128::MAX;
        const CANON_NAN: Self::Bits = 0x7fff8000_00000000_00000000_00000000;
        const INFINITY: Self::Bits = 0x7fff0000_00000000_00000000_00000000;
    }
    pub struct Ieee64;
    impl InnerFloatRepr for Ieee64 {
        type Bits = u64;
        const ZERO: Self::Bits = 0;
        const ONE: Self::Bits = 1;
        const IMPLIED_ONE: Self::Bits = Self::ONE << ((Self::Semantics::PRECISION-1) as i32);
        fn ilog2(bits: &Self::Bits) -> u16 { bits.ilog2() as u16 }
        type Float = Double;
        type Semantics = DoubleS;
    }
    impl FloatRepr for Ieee64 {
        const MAX: Self::Bits = u64::MAX;
        const CANON_NAN: Self::Bits = 0x7ff80000_00000000;
        const INFINITY: Self::Bits = 0x7ff00000_00000000;
    }
    pub struct WideDoubleS;
    impl Semantics for WideDoubleS {
        const BITS: usize = 64 + DoubleS::PRECISION;
        const EXP_BITS: usize = DoubleS::EXP_BITS;
    }
    pub struct Wide64;
    impl InnerFloatRepr for Wide64 {
        type Bits = u128;
        const ZERO: Self::Bits = 0;
        const ONE: Self::Bits = 1;
        const IMPLIED_ONE: Self::Bits = Self::ONE << ((Self::Semantics::PRECISION-1) as i32);
        fn ilog2(bits: &Self::Bits) -> u16 { bits.ilog2() as u16 }
        type Float = IeeeFloat<WideDoubleS>;
        type Semantics = WideDoubleS;
    }
    impl WidenableFloatRepr for Ieee64 {
        type WidenedRepr = Wide64;
        const EXTRA_MASK: <Self::WidenedRepr as InnerFloatRepr>::Bits = !((!Self::WidenedRepr::ZERO >> Self::EXTRA_PRECISION as i32) << Self::EXTRA_PRECISION as i32);
        const EXTRA_TIE: <Self::WidenedRepr as InnerFloatRepr>::Bits = (Self::EXTRA_MASK+<Self::WidenedRepr as InnerFloatRepr>::ONE) >> 1;
    }
    pub struct Ieee32;
    impl InnerFloatRepr for Ieee32 {
        type Bits = u32;
        const ZERO: Self::Bits = 0;
        const ONE: Self::Bits = 1;
        const IMPLIED_ONE: Self::Bits = Self::ONE << ((Self::Semantics::PRECISION-1) as i32);
        fn ilog2(bits: &Self::Bits) -> u16 { bits.ilog2() as u16 }
        type Float = Single;
        type Semantics = SingleS;
    }
    impl FloatRepr for Ieee32 {
        const MAX: Self::Bits = u32::MAX;
        const CANON_NAN: Self::Bits = 0x7fc00000;
        const INFINITY: Self::Bits = 0x7f800000;
    }
    pub struct WideSingleS;
    impl Semantics for WideSingleS {
        const BITS: usize = 32 + SingleS::PRECISION;
        const EXP_BITS: usize = SingleS::EXP_BITS;
    }
    pub struct Wide32;
    impl InnerFloatRepr for Wide32 {
        type Bits = u128;
        const ZERO: Self::Bits = 0;
        const ONE: Self::Bits = 1;
        const IMPLIED_ONE: Self::Bits = Self::ONE << ((Self::Semantics::PRECISION-1) as i32);
        fn ilog2(bits: &Self::Bits) -> u16 { bits.ilog2() as u16 }
        type Float = IeeeFloat<WideSingleS>;
        type Semantics = WideSingleS;
    }
    impl WidenableFloatRepr for Ieee32 {
        type WidenedRepr = Wide32;
        const EXTRA_MASK: <Self::WidenedRepr as InnerFloatRepr>::Bits = !((!Self::WidenedRepr::ZERO >> Self::EXTRA_PRECISION as i32) << Self::EXTRA_PRECISION as i32);
        const EXTRA_TIE: <Self::WidenedRepr as InnerFloatRepr>::Bits = (Self::EXTRA_MASK+<Self::WidenedRepr as InnerFloatRepr>::ONE) >> 1;
    }
    pub trait IeeeBits : Copy + Sized + Ord + Shl<i32, Output=Self> {
        type Repr: FloatRepr<Bits=Self>;
    }
    pub trait WidenableIeeeBits : IeeeBits {
        type WideningRepr: WidenableFloatRepr<Bits=Self>;
    }
    impl IeeeBits for u128 {
        type Repr = Ieee128;
    }
    impl IeeeBits for u64 {
        type Repr = Ieee64;
    }
    impl IeeeBits for u32 {
        type Repr = Ieee32;
    }
    impl WidenableIeeeBits for u64 {
        type WideningRepr = Ieee64;
    }
    impl WidenableIeeeBits for u32 {
        type WideningRepr = Ieee32;
    }
}
use privacy_hack::*;

pub trait Estimator {
    fn estimate_sqrt<B:InnerFloatRepr>(i: B::Bits) -> B::Bits;
}

fn inner_bad_sqrt<E:Estimator, B:InnerFloatRepr>(square: B::Bits, round_mode: Round) -> Result<(StatusAnd<B::Bits>, u32),(B::Bits, u32)> {
    let square_f = B::Float::from_bits(square.into());
    let estimate = E::estimate_sqrt::<B>(square);
    let error = get_error::<B>(estimate, &square_f, round_mode).map_err(|x|(x,0))?;
    let mut iterations = 0;
    let (mut low_estimate, mut low_error);
    let (mut high_estimate, mut high_error);
    // Find the lowest and highest exponents that are, respectively, >= or <=
    // the correct value.
    if error < B::Float::ZERO {
        // our estimate is too low
        (low_estimate, low_error, high_estimate, high_error)
            = minimize_error::<B>(estimate, error, &square_f, &mut iterations, round_mode, |x| x + B::IMPLIED_ONE, Ordering::Greater).map_err(|x|(x,iterations))?;
        assert!(low_error < B::Float::ZERO);
        assert!(high_error > B::Float::ZERO);
    } else if error > B::Float::ZERO {
        // our estimate is too high
        (high_estimate, high_error, low_estimate, low_error)
            = minimize_error::<B>(estimate, error, &square_f, &mut iterations, round_mode, |x| x - B::IMPLIED_ONE, Ordering::Less).map_err(|x|(x,iterations))?;
        assert!(low_error < B::Float::ZERO);
        assert!(high_error > B::Float::ZERO);
    } else {
        // our estimate is just right? uh oh... widen the jaws a bit
        (_, _, low_estimate, low_error)
            = minimize_error::<B>(estimate, error, &square_f, &mut iterations, round_mode, |x| x - B::IMPLIED_ONE, Ordering::Less).map_err(|x|(x,iterations))?;
        (_, _, high_estimate, high_error)
            = minimize_error::<B>(estimate, error, &square_f, &mut iterations, round_mode, |x| x + B::IMPLIED_ONE, Ordering::Greater).map_err(|x|(x,iterations))?;
    }
    /*
    println!("square: {:08X} = {}\r",
        square.into() as u128 as u32,
        f32::from_bits(square.into() as u128 as u32));
    println!("low estimate: {:08X} = {}\r",
        low_estimate.into() as u128 as u32,
        f32::from_bits(low_estimate.into() as u128 as u32));
    println!("high estimate: {:08X} = {}\r",
        high_estimate.into() as u128 as u32,
        f32::from_bits(high_estimate.into() as u128 as u32));
    */
    // Keep adjusting to minimize error, zero in more and more.
    let mut nudge = B::IMPLIED_ONE >> 1;
    while nudge != B::ZERO {
        squeeze_jaws::<B>(
            &mut low_estimate, &mut low_error,
            &mut high_estimate, &mut high_error,
            &mut iterations, &square_f, round_mode, nudge,
        ).map_err(|x|(x,iterations))?;
        nudge >>= 1;
    }
    // low_estimate is now the highest value that squares STRICTLY LOWER than
    // the target, and high_estimate is now the lowest value that squares
    // STRICTLY HIGHER. (all with the current rounding mode)
    // we will give the arithmetic mean of these bit values :3
    let sum = low_estimate + high_estimate;
    let plus = if sum & B::ONE == B::ZERO { B::ZERO } else {
        // oh boy... let's pretend to round it
        match round_mode {
            Round::NearestTiesToEven => if sum & (B::ONE<<1) == B::ZERO {
                B::ZERO
            } else {
                B::ONE
            },
            Round::TowardPositive | Round::NearestTiesToAway => B::ONE,
            Round::TowardZero | Round::TowardNegative => B::ZERO,
        }
    };
    Ok((StatusAnd {
        status: Status::INEXACT,
        value: (sum >> 1) + plus
    }, iterations))
}

fn defined_cases<B:FloatRepr>(square: B::Bits) -> Option<(StatusAnd<B::Bits>, u32)> {
    if square == B::ZERO {
        Some((StatusAnd {
            status: Status::OK,
            value: B::ZERO, // sqrt(0) = 0
        }, 0))
    } else if square == !(B::MAX>>1) {
        Some((StatusAnd {
            status: Status::OK,
            value: !(B::MAX>>1), // sqrt(-0) = -0
        }, 0))
    } else if square & !(B::MAX>>1) != B::ZERO {
        Some((StatusAnd {
            status: Status::INVALID_OP,
            value: B::CANON_NAN, // sqrt(-x) = NaN
        }, 0))
    } else if square == B::INFINITY {
        Some((StatusAnd {
            status: Status::OK,
            value: B::INFINITY,
        }, 0))
    } else if B::get_exponent(&square) > B::MAX_EXPONENT {
        // square root of infinity is NaN, square root of NaN is NaN?
        Some((StatusAnd {
            status: Status::INVALID_OP,
            value: B::CANON_NAN,
        }, 0))
    } else { None }
}

pub fn bad_sqrt_slow<E:Estimator, I:IeeeBits>(square: I, round_mode: Round) -> (StatusAnd<I>, u32) {
    if let Some(special_return) = defined_cases::<I::Repr>(square) {
        special_return
    } else if square < I::Repr::IMPLIED_ONE {
        // Subnormal numbers require slightly special handling.
        // Find out *how* subnormal it is.
        let subnormalcy = (<I::Repr as InnerFloatRepr>::Semantics::PRECISION as u16 - 1) - I::Repr::ilog2(&square);
        let (square, shift_down) = if subnormalcy % 2 == 0 {
            // If it's even, just shift by that amount, and subtract half from
            // the exponent when done. Easy.
            (square << subnormalcy as i32, subnormalcy / 2)
        } else {
            // If it's odd, we're going to have to shift up by one more.
            let mut square = square << subnormalcy as i32;
            I::Repr::add_exponent(&mut square, 1);
            (square, (subnormalcy+1)/2)
        };
        match inner_bad_sqrt::<E,I::Repr>(square, round_mode) {
            Ok(mut x) => {
                I::Repr::subtract_exponent(&mut x.0.value, shift_down);
                x
            },
            Err((mut value, iterations)) => {
                I::Repr::subtract_exponent(&mut value, shift_down);
                (StatusAnd { status: Status::OK, value }, iterations)
            }
        }
    } else {
        match inner_bad_sqrt::<E,I::Repr>(square, round_mode) {
            // inexact or invalid result...
            Ok(x) => x,
            // exact result!
            Err((value, iterations)) => (StatusAnd { status: Status::OK, value }, iterations),
        }
    }
}

pub fn bad_sqrt_slower<E:Estimator, I:WidenableIeeeBits>(square: I, round_mode: Round) -> (StatusAnd<I>, u32) {
    if let Some(special_return) = defined_cases::<I::Repr>(square) {
        special_return
    } else {
        // Since we're widening our input, we don't need to handle subnormals
        // specially on this code path. That's a plus.
        let square = I::WideningRepr::widen(square);
        let (wide_result, iterations) = match inner_bad_sqrt::<E,<I::WideningRepr as WidenableFloatRepr>::WidenedRepr>(square, round_mode) {
            // inexact or invalid result...
            Ok(x) => x,
            // exact result!
            Err((value, iterations)) => (StatusAnd { status: Status::OK, value }, iterations),
        };
        let narrow_result = I::WideningRepr::narrow(wide_result, round_mode);
        (narrow_result, iterations)
    }
}

// Ok(x) -> error value is X
// Err(x) -> exact match to yeet (as in, INEXACT not set so we know it's right)
fn get_error<B: InnerFloatRepr>(root: B::Bits, square_f: &B::Float, round_mode: Round) -> Result<B::Float,B::Bits> {
    let root_f = B::Float::from_bits(root.into());
    let squared_root_f = root_f.mul_r(root_f, round_mode);
    if squared_root_f.value == *square_f && squared_root_f.status == Status::OK {
        // we've got an exact result! yeet it!
        return Err(root)
    }
    Ok((squared_root_f.value.sub_r(*square_f, round_mode)).value)
}

fn minimize_error<B: InnerFloatRepr>(mut best_estimate: B::Bits, best_error: B::Float, square_f: &B::Float, iterations: &mut u32, round_mode: Round, next: impl Fn(B::Bits) -> B::Bits, stop_order: Ordering) -> Result<(B::Bits, B::Float, B::Bits, B::Float),B::Bits> {
    let (mut unstop_estimate, mut unstop_error) = (best_estimate, best_error);
    loop {
        *iterations += 1;
        let new_estimate = next(best_estimate);
        let new_error = get_error::<B>(new_estimate, square_f, round_mode)?;
        match new_error.partial_cmp(&B::Float::ZERO) {
            None | Some(Ordering::Equal) => {
                // can't stop yet, but don't update the unstops
            },
            Some(x) if x == stop_order => {
                return Ok((unstop_estimate, unstop_error, new_estimate, new_error))
            },
            _ => {
                (unstop_estimate, unstop_error) = (new_estimate, new_error);
            },
        }
        (best_estimate, _) = (new_estimate, new_error);
        if *iterations > B::EXPONENT_BIAS as u32 { panic!("minimize_error has fallen into an infinite loop") }
    }
}

fn squeeze_jaws<B: InnerFloatRepr>(low_estimate: &mut B::Bits, low_error: &mut B::Float, high_estimate: &mut B::Bits, high_error: &mut B::Float, iterations: &mut u32, square_f: &B::Float, round_mode: Round, nudge: B::Bits) -> Result<(),B::Bits> {
    debug_assert!(*low_error < B::Float::ZERO);
    debug_assert!(*high_error > B::Float::ZERO);
    // raise the lower jaw
    loop {
        *iterations += 1;
        let next_estimate = *low_estimate + nudge;
        let next_error = get_error::<B>(next_estimate, &square_f, round_mode)?;
        match next_error.partial_cmp(&B::Float::ZERO) {
            Some(Ordering::Less) => {
                *low_estimate = next_estimate;
                *low_error = next_error;
                continue;
            },
            None | Some(Ordering::Equal) => {
                break;
            },
            Some(Ordering::Greater) => {
                *high_estimate = next_estimate;
                *high_error = next_error;
                return Ok(()); // new upper jaw
            },
        }
    }
    // lower the upper jaw
    loop {
        *iterations += 1;
        let next_estimate = *high_estimate - nudge;
        let next_error = get_error::<B>(next_estimate, &square_f, round_mode)?;
        match next_error.partial_cmp(&B::Float::ZERO) {
            Some(Ordering::Less) => {
                // if nudge was greater than the valid range, this would have
                // been caught in the "raise the lower jaw" step
                unreachable!()
            },
            None | Some(Ordering::Equal) => {
                break;
            },
            Some(Ordering::Greater) => {
                *high_estimate = next_estimate;
                *high_error = next_error;
            },
        }
    }
    Ok(())
}

pub struct BadEstimator;
impl Estimator for BadEstimator {
    fn estimate_sqrt<B:InnerFloatRepr>(i: B::Bits) -> B::Bits {
        let src_exponent = B::get_exponent(&i);
        let dst_exponent = src_exponent / 2;
        B::from_exponent_and_significand(dst_exponent, B::IMPLIED_ONE)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn easy_mode() {
        let (result, iterations) = bad_sqrt_slow::<BadEstimator,u32>((4.0f32).to_bits(), Round::NearestTiesToAway);
        println!("Square root of 4: {iterations} iterations");
        assert_eq!(result, StatusAnd {
            value: (2.0f32).to_bits(),
            status: Status::OK,
        });
    }
    #[test]
    fn zero() {
        let (result, iterations) = bad_sqrt_slow::<BadEstimator,u32>(0, Round::NearestTiesToAway);
        println!("Square root of 0: {iterations} iterations");
        assert_eq!(result, StatusAnd {
            value: (0.0f32).to_bits(),
            status: Status::OK,
        });
    }
    #[test]
    fn the_infinite_nan() {
        assert_eq!(bad_sqrt_slow::<BadEstimator,u32>(Ieee32::INFINITY, Round::NearestTiesToAway), (StatusAnd {
            value: Ieee32::INFINITY,
            status: Status::OK,
        }, 0));
        assert_eq!(bad_sqrt_slow::<BadEstimator,u32>(Ieee32::INFINITY+1, Round::NearestTiesToAway), (StatusAnd {
            value: Ieee32::CANON_NAN,
            status: Status::INVALID_OP,
        }, 0));
        assert_eq!(bad_sqrt_slow::<BadEstimator,u32>(Ieee32::INFINITY|0x80000000, Round::NearestTiesToAway), (StatusAnd {
            value: Ieee32::CANON_NAN,
            status: Status::INVALID_OP,
        }, 0));
        assert_eq!(bad_sqrt_slow::<BadEstimator,u32>(Ieee32::INFINITY|0x80000001, Round::NearestTiesToAway), (StatusAnd {
            value: Ieee32::CANON_NAN,
            status: Status::INVALID_OP,
        }, 0));
    }
    #[test] #[ignore]
    fn subnormal_test() {
        for n in 1 .. 8388608u32 {
            let (result, _iterations) = bad_sqrt_slow::<BadEstimator,u32>(n, Round::NearestTiesToAway);
            let root = Single::from_bits(result.value as u128);
            let square = root * root;
            assert_eq!(square.value, Single::from_bits(n as u128))
        }
    }
    #[test]
    fn fuzz_data() {
        const TEST_CASES: &[(u32, u32)] = &[
            (0x527FFFFF, 0x48FFFFFF),
            (0x3D800001, 0x3E800000),
        ];
        for (question, answer) in TEST_CASES.iter() {
            let (result, _iterations) = bad_sqrt_slower::<BadEstimator,u32>(*question, Round::NearestTiesToEven);
            assert_eq!(*answer, result.value);
        }
    }
}
