//! Exponentiation for fixed-point numbers.
//!
//! # Usage
//!
//! ```rust
//! use fixed::types::I32F32;
//! use fixed_exp::{FixedPowI, FixedPowF};
//!
//! let x = I32F32::from_num(4.0);
//! assert_eq!(I32F32::from_num(1024.0), x.powi(5));
//! assert_eq!(I32F32::from_num(8.0), x.powf(I32F32::from_num(1.5)));
//! ```

use std::cmp::{Ord, Ordering};

use fixed::traits::Fixed;
use fixed::types::extra::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8};
use fixed::{
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use num_traits::{One, PrimInt, Zero};
use typenum::{
    Bit, IsLessOrEqual, LeEq, True, Unsigned, U126, U127, U14, U15, U30, U31, U6, U62, U63, U7,
};

/// Trait alias for fixed-points numbers that support both integer and fixed-point exponentiation.
pub trait FixedPow: Fixed + FixedPowI + FixedPowF {}
impl<T: Fixed + FixedPowI + FixedPowF> FixedPow for T {}

/// Extension trait providing integer exponentiation for fixed-point numbers.
pub trait FixedPowI: Fixed {
    /// Raises a number to an integer power, using exponentiation by squaring.
    ///
    /// Using this function is generally faster than using `powf`.
    ///
    /// # Panics
    ///
    /// Panics if `1` cannot be represented in `Self`, and `n` is non-positive.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::types::I32F32;
    /// use fixed_exp::FixedPowI;
    ///
    /// let x = I32F32::from_num(4.0);
    /// assert_eq!(I32F32::from_num(1024.0), x.powi(5));
    /// ```
    fn powi(self, n: i32) -> Self;
}

/// Extension trait providing fixed-point exponentiation for fixed-point numbers.
///
/// This is only implemented for types that can represent numbers larger than `1`.
pub trait FixedPowF: Fixed {
    /// Raises a number to a fixed-point power.
    ///
    /// # Panics
    ///
    /// - If `self` is negative and `n` is fractional.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::types::I32F32;
    /// use fixed_exp::FixedPowF;
    ///
    /// let x = I32F32::from_num(4.0);
    /// assert_eq!(I32F32::from_num(8.0), x.powf(I32F32::from_num(1.5)));
    /// ```
    fn powf(self, n: Self) -> Self;
}

fn powi_positive<T: Fixed>(mut x: T, mut n: i32) -> T {
    assert!(n > 0, "exponent should be positive");

    let mut acc = x;
    n -= 1;

    while n > 0 {
        if n & 1 == 1 {
            acc *= x;
        }
        x *= x;
        n >>= 1;
    }

    acc
}

fn sqrt<T>(x: T) -> T
where
    T: Fixed + Helper,
    T::Bits: PrimInt,
{
    if x.is_zero() || x.is_one() {
        return x;
    }

    let mut pow2 = T::one();
    let mut result;

    if x < T::one() {
        while x <= pow2 * pow2 {
            pow2 >>= 1;
        }

        result = pow2;
    } else {
        // x >= T::one()
        while pow2 * pow2 <= x {
            pow2 <<= 1;
        }

        result = pow2 >> 1;
    }

    for _ in 0..T::NUM_BITS {
        pow2 >>= 1;
        let next_result = result + pow2;
        if next_result * next_result <= x {
            result = next_result;
        }
    }

    result
}

fn powf_01<T>(mut x: T, n: T) -> T
where
    T: Fixed + Helper,
    T::Bits: PrimInt + std::fmt::Debug,
{
    let mut n = n.to_bits();
    if n.is_zero() {
        panic!("fractional exponent should not be zero");
    }

    let top = T::Bits::one() << ((T::Frac::U32 - 1) as usize);
    let mask = !(T::Bits::one() << ((T::Frac::U32) as usize));
    let mut acc = None;

    while !n.is_zero() {
        x = sqrt(x);
        if !(n & top).is_zero() {
            acc = match acc {
                Some(acc) => Some(acc * x),
                None => Some(x),
            };
        }
        n = (n << 1) & mask;
    }

    acc.unwrap()
}

fn powf_positive<T>(x: T, n: T) -> T
where
    T: Fixed + Helper,
    T::Bits: PrimInt + std::fmt::Debug,
{
    assert!(Helper::is_positive(n), "exponent should be positive");

    let powi = powi_positive(x, n.int().to_num());
    let frac = n.frac();

    if frac.is_zero() {
        powi
    } else {
        assert!(Helper::is_positive(x), "base should be positive");
        powi * powf_01(x, frac)
    }
}

macro_rules! impl_fixed_pow {
    ($fixed:ident, $le_eq:ident, $le_eq_one:ident) => {
        impl<Frac> FixedPowI for $fixed<Frac>
        where
            Frac: $le_eq + IsLessOrEqual<$le_eq_one>,
        {
            fn powi(self, n: i32) -> Self {
                if !<LeEq<Frac, $le_eq_one>>::BOOL && n <= 0 {
                    panic!(
                        "cannot raise `{}` to the power of `{}` because numbers larger than or equal to `1` are not representable",
                        self, n
                    );
                }

                match n.cmp(&0) {
                    Ordering::Greater => powi_positive(self, n),
                    Ordering::Equal => Self::from_bits(1 << Frac::U32),
                    Ordering::Less => powi_positive(Self::from_bits(1 << Frac::U32) / self, -n),
                }
            }
        }

        impl<Frac> FixedPowF for $fixed<Frac>
        where
            Frac: $le_eq + IsLessOrEqual<$le_eq_one, Output = True>,
        {
            fn powf(self, n: Self) -> Self {
                let zero = Self::from_bits(0);

                if !<LeEq<Frac, $le_eq_one>>::BOOL && n <= zero {
                    panic!(
                        "cannot raise `{}` to the power of `{}` because numbers larger than or equal to `1` are not representable",
                        self, n
                    );
                }

                match n.cmp(&zero) {
                    Ordering::Greater => powf_positive(self, n),
                    Ordering::Equal => Self::from_bits(1 << Frac::U32),
                    Ordering::Less => powf_positive(Self::from_bits(1 << Frac::U32) / self, Helper::neg(n)),
                }
            }
        }
    };
}

impl_fixed_pow!(FixedI8, LeEqU8, U6);
impl_fixed_pow!(FixedI16, LeEqU16, U14);
impl_fixed_pow!(FixedI32, LeEqU32, U30);
impl_fixed_pow!(FixedI64, LeEqU64, U62);
impl_fixed_pow!(FixedI128, LeEqU128, U126);

impl_fixed_pow!(FixedU8, LeEqU8, U7);
impl_fixed_pow!(FixedU16, LeEqU16, U15);
impl_fixed_pow!(FixedU32, LeEqU32, U31);
impl_fixed_pow!(FixedU64, LeEqU64, U63);
impl_fixed_pow!(FixedU128, LeEqU128, U127);

trait Helper {
    const NUM_BITS: u32;
    fn is_positive(self) -> bool;
    fn is_zero(self) -> bool;
    fn is_one(self) -> bool;
    fn one() -> Self;
    fn neg(self) -> Self;
}

macro_rules! impl_sign_helper {
    (signed, $fixed:ident, $le_eq:ident, $le_eq_one:ident) => {
        impl<Frac: $le_eq> Helper for $fixed<Frac>
        where
            Frac: $le_eq + IsLessOrEqual<$le_eq_one>,
        {
            const NUM_BITS: u32 = <Self as Fixed>::INT_NBITS + <Self as Fixed>::FRAC_NBITS;
            fn is_positive(self) -> bool {
                $fixed::is_positive(self)
            }
            fn is_zero(self) -> bool {
                self.to_bits() == 0
            }
            fn is_one(self) -> bool {
                <LeEq<Frac, $le_eq_one>>::BOOL && self.to_bits() == 1 << Frac::U32
            }
            fn one() -> Self {
                assert!(
                    <LeEq<Frac, $le_eq_one>>::BOOL,
                    "one should be possible to represent"
                );
                Self::from_bits(1 << Frac::U32)
            }
            fn neg(self) -> Self {
                -self
            }
        }
    };
    (unsigned, $fixed:ident, $le_eq:ident, $le_eq_one:ident) => {
        impl<Frac: $le_eq> Helper for $fixed<Frac>
        where
            Frac: $le_eq + IsLessOrEqual<$le_eq_one>,
        {
            const NUM_BITS: u32 = <Self as Fixed>::INT_NBITS + <Self as Fixed>::FRAC_NBITS;
            fn is_positive(self) -> bool {
                self != Self::from_bits(0)
            }
            fn is_zero(self) -> bool {
                self.to_bits() == 0
            }
            fn is_one(self) -> bool {
                <LeEq<Frac, $le_eq_one>>::BOOL && self.to_bits() == 1 << Frac::U32
            }
            fn one() -> Self {
                assert!(
                    <LeEq<Frac, $le_eq_one>>::BOOL,
                    "one should be possible to represent"
                );
                Self::from_bits(1 << Frac::U32)
            }
            fn neg(self) -> Self {
                panic!("cannot negate an unsigned number")
            }
        }
    };
}

impl_sign_helper!(signed, FixedI8, LeEqU8, U6);
impl_sign_helper!(signed, FixedI16, LeEqU16, U14);
impl_sign_helper!(signed, FixedI32, LeEqU32, U30);
impl_sign_helper!(signed, FixedI64, LeEqU64, U62);
impl_sign_helper!(signed, FixedI128, LeEqU128, U126);

impl_sign_helper!(unsigned, FixedU8, LeEqU8, U7);
impl_sign_helper!(unsigned, FixedU16, LeEqU16, U15);
impl_sign_helper!(unsigned, FixedU32, LeEqU32, U31);
impl_sign_helper!(unsigned, FixedU64, LeEqU64, U63);
impl_sign_helper!(unsigned, FixedU128, LeEqU128, U127);

#[cfg(test)]
mod tests {
    use super::*;

    use fixed::types::{I1F31, I32F32, U0F32, U32F32};

    fn powi_positive_naive<T: Fixed>(x: T, n: i32) -> T {
        assert!(n > 0, "exponent should be positive");
        let mut acc = x;
        for _ in 1..n {
            acc *= x;
        }
        acc
    }

    fn delta<T: Fixed>(a: T, b: T) -> T {
        Ord::max(a, b) - Ord::min(a, b)
    }

    #[test]
    fn test_powi_positive() {
        let epsilon = I32F32::from_num(0.0001);

        let test_cases = &[
            (I32F32::from_num(1.0), 42),
            (I32F32::from_num(0.8), 7),
            (I32F32::from_num(1.2), 11),
            (I32F32::from_num(2.6), 16),
            (I32F32::from_num(-2.2), 4),
            (I32F32::from_num(-2.2), 5),
        ];

        for &(x, n) in test_cases {
            assert!((powi_positive_naive(x, n) - x.powi(n)).abs() < epsilon);
        }

        let epsilon = U32F32::from_num(0.0001);

        let test_cases = &[
            (U32F32::from_num(1.0), 42),
            (U32F32::from_num(0.8), 7),
            (U32F32::from_num(1.2), 11),
            (U32F32::from_num(2.6), 16),
        ];

        for &(x, n) in test_cases {
            assert!(delta(powi_positive_naive(x, n), x.powi(n)) < epsilon);
        }
    }

    #[test]
    fn test_powi_positive_sub_one() {
        let epsilon = I1F31::from_num(0.0001);

        let test_cases = &[
            (I1F31::from_num(0.5), 3),
            (I1F31::from_num(0.8), 5),
            (I1F31::from_num(0.2), 7),
            (I1F31::from_num(0.6), 9),
            (I1F31::from_num(-0.6), 3),
            (I1F31::from_num(-0.6), 4),
        ];

        for &(x, n) in test_cases {
            assert!((powi_positive_naive(x, n) - x.powi(n)).abs() < epsilon);
        }

        let epsilon = U0F32::from_num(0.0001);

        let test_cases = &[
            (U0F32::from_num(0.5), 3),
            (U0F32::from_num(0.8), 5),
            (U0F32::from_num(0.2), 7),
            (U0F32::from_num(0.6), 9),
        ];

        for &(x, n) in test_cases {
            assert!(delta(powi_positive_naive(x, n), x.powi(n)) < epsilon);
        }
    }

    #[test]
    fn test_powi_non_positive() {
        let epsilon = I32F32::from_num(0.0001);

        let test_cases = &[
            (I32F32::from_num(1.0), -17),
            (I32F32::from_num(0.8), -7),
            (I32F32::from_num(1.2), -9),
            (I32F32::from_num(2.6), -3),
        ];

        for &(x, n) in test_cases {
            assert!((powi_positive_naive(I32F32::from_num(1) / x, -n) - x.powi(n)).abs() < epsilon);
        }

        assert_eq!(I32F32::from_num(1), I32F32::from_num(42).powi(0));
        assert_eq!(I32F32::from_num(1), I32F32::from_num(-42).powi(0));
        assert_eq!(I32F32::from_num(1), I32F32::from_num(0).powi(0));
    }

    fn powf_float<T: Fixed>(x: T, n: T) -> T {
        let x: f64 = x.to_num();
        let n: f64 = n.to_num();
        T::from_num(x.powf(n))
    }

    #[test]
    fn test_powf() {
        let epsilon = I32F32::from_num(0.0001);

        let test_cases = &[
            (I32F32::from_num(1.0), I32F32::from_num(7.2)),
            (I32F32::from_num(0.8), I32F32::from_num(-4.5)),
            (I32F32::from_num(1.2), I32F32::from_num(5.0)),
            (I32F32::from_num(2.6), I32F32::from_num(-6.7)),
            (I32F32::from_num(-1.2), I32F32::from_num(4.0)),
            (I32F32::from_num(-1.2), I32F32::from_num(-3.0)),
        ];

        for &(x, n) in test_cases {
            assert!((powf_float(x, n) - x.powf(n)).abs() < epsilon);
        }

        let epsilon = U32F32::from_num(0.0001);

        let test_cases = &[
            (U32F32::from_num(1.0), U32F32::from_num(7.2)),
            (U32F32::from_num(0.8), U32F32::from_num(4.5)),
            (U32F32::from_num(1.2), U32F32::from_num(5.0)),
            (U32F32::from_num(2.6), U32F32::from_num(6.7)),
        ];

        for &(x, n) in test_cases {
            assert!(delta(powf_float(x, n), x.powf(n)) < epsilon);
        }
    }
}
