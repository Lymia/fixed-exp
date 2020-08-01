//! Exponentiation for fixed-point numbers.
//!
//! # Usage
//!
//! ```rust
//! use fixed::types::I32F32;
//! use fixed_exp::FixedPow;
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
use typenum::{Bit, IsLessOrEqual, LeEq, U126, U127, U14, U15, U30, U31, U6, U62, U63, U7};

/// Extension trait providing exponentiation methods for fixed-point numbers.
pub trait FixedPow: Fixed {
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
    /// use fixed_exp::FixedPow;
    ///
    /// let x = I32F32::from_num(4.0);
    /// assert_eq!(I32F32::from_num(1024.0), x.powi(5));
    /// ```
    fn powi(self, n: i32) -> Self;

    /// Raises a number to a fixed-point power.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::types::I32F32;
    /// use fixed_exp::FixedPow;
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

macro_rules! impl_fixed_pow {
    ($fixed:ident, $le_eq:ident, $le_eq_one:ident) => {
        impl<Frac> FixedPow for $fixed<Frac>
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

            fn powf(self, n: Self) -> Self {
                unimplemented!("powf is unimplemented");
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
}
