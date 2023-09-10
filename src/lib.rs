use std::cmp::Ordering;

use rustc_apfloat::{Float, Round, StatusAnd, Status, ieee::Semantics};

mod privacy_hack {
    use std::{
        fmt::Debug,
        ops::{Add, AddAssign, BitAnd, BitOr, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign},
    };
    use rustc_apfloat::ieee::Semantics;
    pub trait FloatBits :
        Copy + Debug + Eq + Ord
        + Add<Output=Self>
        + AddAssign<Self>
        + Sub<Output=Self>
        + SubAssign<Self>
        + Shr<i32, Output=Self>
        + ShrAssign<i32>
        + Shl<i32, Output=Self>
        + ShlAssign<i32>
        + Not<Output=Self>
        + BitOr<Self, Output=Self>
        + BitAnd<Self, Output=Self>
        + Into<u128>
        + From<u16>
    {
        const MAX: Self;
        const ZERO: Self;
        const ONE: Self;
        /// The NaN bit value mandated by the RISC-V specification
        const CANON_NAN: Self;
        const INFINITY: Self;
        const EXPONENT_BIAS: i16 = Self::Semantics::MAX_EXP as i16;
        const MAX_EXPONENT: i16 = Self::Semantics::MAX_EXP as i16;
        const IMPLIED_ONE: Self;
        type Float: rustc_apfloat::Float + Debug;
        type Semantics: rustc_apfloat::ieee::Semantics;
        fn ilog2(&self) -> u16;
        fn get_exponent(&self) -> i16 {
            debug_assert!(*self & !(Self::MAX >> 1) == Self::ZERO);
            (*self >> ((Self::Semantics::PRECISION-1) as i32))
                .into() as i16 - Self::EXPONENT_BIAS
        }
        // this only works if we don't borrow/carry through the sign bit...
        // we will only be calling these on numbers that have plenty of
        // room above and below, so we should be fine.
        fn add_exponent(&mut self, value: u16) {
            *self += Self::from(value) << (Self::Semantics::PRECISION-1) as i32
        }
        fn subtract_exponent(&mut self, value: u16) {
            *self -= Self::from(value) << (Self::Semantics::PRECISION-1) as i32
        }
        fn get_significand(&self) -> Self {
            if self.get_exponent() == -Self::EXPONENT_BIAS {
                // subnormal number
                (*self & (Self::IMPLIED_ONE-Self::ONE)) << 1
                // (shift left by 1 to compensate for the wrong exponent being
                // returned)
            } else {
                *self & (Self::IMPLIED_ONE-Self::ONE) | Self::IMPLIED_ONE
            }
        }
        fn from_exponent_and_significand(mut exponent: i16, mut significand: Self) -> Self {
            while significand > Self::IMPLIED_ONE {
                significand >>= 1;
                exponent += 1;
            }
            while significand <= Self::IMPLIED_ONE>>1 {
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
                (significand & !Self::IMPLIED_ONE) | (Self::from((exponent + Self::EXPONENT_BIAS) as u16) << (Self::Semantics::PRECISION-1) as i32)
            }
        }
    }
    impl FloatBits for u128 {
        const MAX: Self = u128::MAX;
        const ZERO: Self = 0;
        const ONE: Self = 1;
        const IMPLIED_ONE: Self = Self::ONE << ((Self::Semantics::PRECISION-1) as i32);
        const CANON_NAN: Self = 0x7fff8000_00000000_00000000_00000000;
        const INFINITY: Self = 0x7fff0000_00000000_00000000_00000000;
        fn ilog2(&self) -> u16 { u128::ilog2(*self) as u16 }
        type Float = rustc_apfloat::ieee::Quad;
        type Semantics = rustc_apfloat::ieee::QuadS;
    }
    impl FloatBits for u64 {
        const MAX: Self = u64::MAX;
        const ZERO: Self = 0;
        const ONE: Self = 1;
        const IMPLIED_ONE: Self = Self::ONE << ((Self::Semantics::PRECISION-1) as i32);
        const CANON_NAN: Self = 0x7ff80000_00000000;
        const INFINITY: Self = 0x7ff00000_00000000;
        fn ilog2(&self) -> u16 { u64::ilog2(*self) as u16 }
        type Float = rustc_apfloat::ieee::Double;
        type Semantics = rustc_apfloat::ieee::DoubleS;
    }
    impl FloatBits for u32 {
        const MAX: Self = u32::MAX;
        const ZERO: Self = 0;
        const ONE: Self = 1;
        const IMPLIED_ONE: Self = Self::ONE << ((Self::Semantics::PRECISION-1) as i32);
        const CANON_NAN: Self = 0x7fc00000;
        const INFINITY: Self = 0x7f800000;
        fn ilog2(&self) -> u16 { u32::ilog2(*self) as u16 }
        type Float = rustc_apfloat::ieee::Single;
        type Semantics = rustc_apfloat::ieee::SingleS;
    }
}
use privacy_hack::FloatBits;

pub trait Estimator {
    fn estimate_sqrt<B:FloatBits>(i: B) -> B;
}

fn inner_bad_sqrt<E:Estimator, B:FloatBits>(square: B, round_mode: Round) -> Result<(StatusAnd<B>, u32),(B, u32)> {
    let square_f = B::Float::from_bits(square.into());
    let estimate = E::estimate_sqrt(square);
    let error = get_error(estimate, &square_f, round_mode).map_err(|x|(x,0))?;
    let mut iterations = 0;
    let (mut low_estimate, mut low_error);
    let (mut high_estimate, mut high_error);
    // Find the lowest and highest exponents that are, respectively, >= or <=
    // the correct value.
    if error < B::Float::ZERO {
        // our estimate is too low
        (low_estimate, low_error, high_estimate, high_error)
            = minimize_error(estimate, error, &square_f, &mut iterations, round_mode, |x| x + B::IMPLIED_ONE, Ordering::Greater).map_err(|x|(x,iterations))?;
        assert!(low_error < B::Float::ZERO);
        assert!(high_error > B::Float::ZERO);
    } else if error > B::Float::ZERO {
        // our estimate is too high
        (high_estimate, high_error, low_estimate, low_error)
            = minimize_error(estimate, error, &square_f, &mut iterations, round_mode, |x| x - B::IMPLIED_ONE, Ordering::Less).map_err(|x|(x,iterations))?;
        assert!(low_error < B::Float::ZERO);
        assert!(high_error > B::Float::ZERO);
    } else {
        // our estimate is just right? uh oh... widen the jaws a bit
        (_, _, low_estimate, low_error)
            = minimize_error(estimate, error, &square_f, &mut iterations, round_mode, |x| x - B::IMPLIED_ONE, Ordering::Less).map_err(|x|(x,iterations))?;
        (_, _, high_estimate, high_error)
            = minimize_error(estimate, error, &square_f, &mut iterations, round_mode, |x| x + B::IMPLIED_ONE, Ordering::Greater).map_err(|x|(x,iterations))?;
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
        squeeze_jaws(
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

pub fn bad_sqrt<E:Estimator, B:FloatBits>(square: B, round_mode: Round) -> (StatusAnd<B>, u32) {
    if square == B::ZERO {
        return (StatusAnd {
            status: Status::OK,
            value: B::ZERO, // sqrt(0) = 0
        }, 0)
    } else if square == !(B::MAX>>1) {
        return (StatusAnd {
            status: Status::OK,
            value: !(B::MAX>>1), // sqrt(-0) = -0
        }, 0)
    } else if square & !(B::MAX>>1) != B::ZERO {
        return (StatusAnd {
            status: Status::INVALID_OP,
            value: B::CANON_NAN, // sqrt(-x) = NaN
        }, 0)
    } else if square == B::INFINITY {
        return (StatusAnd {
            status: Status::OK,
            value: B::INFINITY,
        }, 0)
    } else if square.get_exponent() > B::MAX_EXPONENT {
        // square root of infinity is NaN, square root of NaN is NaN?
        return (StatusAnd {
            status: Status::INVALID_OP,
            value: B::CANON_NAN,
        }, 0)
    } else if square < B::IMPLIED_ONE {
        // Subnormal numbers require slightly special handling.
        // Find out *how* subnormal it is.
        let subnormalcy = (B::Semantics::PRECISION as u16 - 1) - square.ilog2();
        let (square, shift_down) = if subnormalcy % 2 == 0 {
            // If it's even, just shift by that amount, and subtract half from
            // the exponent when done. Easy.
            (square << subnormalcy as i32, subnormalcy / 2)
        } else {
            // If it's odd, we're going to have to shift up by one more.
            let mut square = square << subnormalcy as i32;
            square.add_exponent(1);
            (square, (subnormalcy+1)/2)
        };
        match inner_bad_sqrt::<E,B>(square, round_mode) {
            Ok(mut x) => {
                x.0.value.subtract_exponent(shift_down);
                x
            },
            Err((mut value, iterations)) => {
                value.subtract_exponent(shift_down);
                (StatusAnd { status: Status::OK, value }, iterations)
            }
        }
    } else {
        match inner_bad_sqrt::<E,B>(square, round_mode) {
            // inexact or invalid result...
            Ok(x) => x,
            // exact result!
            Err((value, iterations)) => (StatusAnd { status: Status::OK, value }, iterations),
        }
    }
}

fn get_error<B: FloatBits>(root: B, square_f: &B::Float, round_mode: Round) -> Result<B::Float,B> {
    let root_f = B::Float::from_bits(root.into());
    let squared_root_f = root_f.mul_r(root_f, round_mode);
    if squared_root_f.value == *square_f && squared_root_f.status == Status::OK {
        // we've got an exact result! yeet it!
        return Err(root)
    }
    Ok((squared_root_f.value.sub_r(*square_f, round_mode)).value)
}

fn minimize_error<B: FloatBits>(mut best_estimate: B, best_error: B::Float, square_f: &B::Float, iterations: &mut u32, round_mode: Round, next: impl Fn(B) -> B, stop_order: Ordering) -> Result<(B, B::Float, B, B::Float),B> {
    let (mut unstop_estimate, mut unstop_error) = (best_estimate, best_error);
    loop {
        *iterations += 1;
        let new_estimate = next(best_estimate);
        let new_error = get_error(new_estimate, square_f, round_mode)?;
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

fn squeeze_jaws<B: FloatBits>(low_estimate: &mut B, low_error: &mut B::Float, high_estimate: &mut B, high_error: &mut B::Float, iterations: &mut u32, square_f: &B::Float, round_mode: Round, nudge: B) -> Result<(),B> {
    debug_assert!(*low_error < B::Float::ZERO);
    debug_assert!(*high_error > B::Float::ZERO);
    // raise the lower jaw
    loop {
        *iterations += 1;
        let next_estimate = *low_estimate + nudge;
        let next_error = get_error(next_estimate, &square_f, round_mode)?;
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
        let next_error = get_error(next_estimate, &square_f, round_mode)?;
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
    fn estimate_sqrt<B:FloatBits>(i: B) -> B {
        let src_exponent = i.get_exponent();
        let dst_exponent = src_exponent / 2;
        B::from_exponent_and_significand(dst_exponent, B::IMPLIED_ONE)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn easy_mode() {
        let (result, iterations) = bad_sqrt::<BadEstimator,u32>((4.0f32).to_bits(), Round::NearestTiesToAway);
        println!("Square root of 4: {iterations} iterations");
        assert_eq!(result, StatusAnd {
            value: (2.0f32).to_bits(),
            status: Status::OK,
        });
    }
    #[test]
    fn zero() {
        let (result, iterations) = bad_sqrt::<BadEstimator,u32>(0, Round::NearestTiesToAway);
        println!("Square root of 0: {iterations} iterations");
        assert_eq!(result, StatusAnd {
            value: (0.0f32).to_bits(),
            status: Status::OK,
        });
    }
    #[test]
    fn the_infinite_nan() {
        assert_eq!(bad_sqrt::<BadEstimator,u32>(u32::INFINITY, Round::NearestTiesToAway), (StatusAnd {
            value: u32::INFINITY,
            status: Status::OK,
        }, 0));
        assert_eq!(bad_sqrt::<BadEstimator,u32>(u32::INFINITY+1, Round::NearestTiesToAway), (StatusAnd {
            value: u32::CANON_NAN,
            status: Status::INVALID_OP,
        }, 0));
        assert_eq!(bad_sqrt::<BadEstimator,u32>(u32::INFINITY|0x80000000, Round::NearestTiesToAway), (StatusAnd {
            value: u32::CANON_NAN,
            status: Status::INVALID_OP,
        }, 0));
        assert_eq!(bad_sqrt::<BadEstimator,u32>(u32::INFINITY|0x80000001, Round::NearestTiesToAway), (StatusAnd {
            value: u32::CANON_NAN,
            status: Status::INVALID_OP,
        }, 0));
    }
    #[test] #[ignore]
    fn subnormal_test() {
        use rustc_apfloat::ieee::Single;
        for n in 1 .. 8388608u32 {
            let (result, _iterations) = bad_sqrt::<BadEstimator,u32>(n, Round::NearestTiesToAway);
            let root = Single::from_bits(result.value as u128);
            let square = root * root;
            assert_eq!(square.value, Single::from_bits(n as u128))
        }
    }
}
