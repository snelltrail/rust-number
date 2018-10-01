use std::cmp::Ordering;
use std::num::ParseIntError;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::str::FromStr;

use uint::UInt;

#[derive(Debug, Eq, PartialEq, Clone)]
enum Sign {
    Zero,
    Positive,
    Negative,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Int {
    magnitude: UInt,
    sign: Sign,
}

impl From<i32> for Int {
    fn from(num: i32) -> Self {
        Int {
            magnitude: UInt::from(abs(num)),
            sign: if num == 0 {
                Sign::Zero
            } else if num > 0 {
                Sign::Positive
            } else {
                Sign::Negative
            },
        }
    }
}

impl FromStr for Int {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let first_char = s.chars().next().unwrap();
        let is_negative = first_char == '-';
        Ok(Int {
            magnitude: if is_negative {
                UInt::from_str(&s[1..]).unwrap()
            } else {
                UInt::from_str(s).unwrap()
            },
            sign: match first_char {
                '-' => Sign::Negative,
                '0' if s.len() == 1 => Sign::Zero,
                _ => Sign::Positive,
            },
        })
    }
}

impl<'a> Neg for &'a Int {
    type Output = Int;

    fn neg(self) -> Int {
        -self.clone()
    }
}

impl Neg for Int {
    type Output = Int;

    fn neg(mut self) -> Int {
        self.sign = match self.sign {
            Sign::Zero => Sign::Zero,
            Sign::Positive => Sign::Negative,
            Sign::Negative => Sign::Positive,
        };
        self
    }
}

impl<'a> AddAssign<&'a Int> for Int {
    fn add_assign(&mut self, other: &Int) {
        if self.sign == Sign::Zero {
            *self = other.clone();
        } else if self.sign == Sign::Positive {
            if other.sign == Sign::Zero || other.sign == Sign::Positive {
                self.magnitude += &other.magnitude;
            } else {
                assert!(other.sign == Sign::Negative);
                match self.magnitude.cmp(&other.magnitude) {
                    Ordering::Equal => *self = Int::from(0),
                    Ordering::Greater => self.magnitude -= &other.magnitude,
                    Ordering::Less => {
                        let mut temp = other.clone();
                        temp.magnitude -= &self.magnitude;
                        *self = temp;
                    }
                }
            }
        } else {
            assert!(self.sign == Sign::Negative);
            if other.sign == Sign::Zero || other.sign == Sign::Negative {
                self.magnitude += &other.magnitude;
            } else {
                assert!(other.sign == Sign::Positive);
                match self.magnitude.cmp(&other.magnitude) {
                    Ordering::Equal => *self = Int::from(0),
                    Ordering::Greater => self.magnitude -= &other.magnitude,
                    Ordering::Less => {
                        let mut temp = other.clone();
                        temp.magnitude -= &self.magnitude;
                        *self = temp;
                    }
                }
            }
        }
    }
}

impl<'a, 'b> Add<&'b Int> for &'a Int {
    type Output = Int;

    fn add(self, other: &Int) -> Int {
        let mut self_clone = self.clone();
        self_clone += other;
        self_clone
    }
}

impl<'a> Add<Int> for &'a Int {
    type Output = Int;

    fn add(self, mut other: Int) -> Int {
        other += self;
        other
    }
}

impl<'a> Add<&'a Int> for Int {
    type Output = Int;

    fn add(mut self, other: &Int) -> Int {
        self += other;
        self
    }
}

impl Add<Int> for Int {
    type Output = Int;

    fn add(mut self, other: Int) -> Int {
        self += &other;
        self
    }
}

impl<'a> SubAssign<&'a Int> for Int {
    fn sub_assign(&mut self, other: &Int) {
        *self = self.clone() - other;
    }
}

////TODO: Implement Sub using SubAssign to avoid unnecessary copies
impl<'a, 'b> Sub<&'b Int> for &'a Int {
    type Output = Int;

    fn sub(self, other: &Int) -> Int {
        self + (-other)
    }
}

impl<'a> Sub<Int> for &'a Int {
    type Output = Int;

    fn sub(self, other: Int) -> Int {
        self + (-other)
    }
}

impl<'a> Sub<&'a Int> for Int {
    type Output = Int;

    fn sub(self, other: &Int) -> Int {
        self + (-other)
    }
}

impl Sub<Int> for Int {
    type Output = Int;

    fn sub(self, other: Int) -> Int {
        self + (-other)
    }
}

impl<'a> MulAssign<&'a Int> for Int {
    fn mul_assign(&mut self, other: &Int) {
        if self.sign == Sign::Zero || other.sign == Sign::Zero {
            *self = Int::from(0);
        } else {
            self.magnitude *= &other.magnitude;
            if self.sign == other.sign && self.sign == Sign::Negative {
                self.sign = Sign::Positive;
            } else if self.sign != other.sign {
                if self.sign != Sign::Negative {
                    self.sign = Sign::Negative;
                }
            }
        }
    }
}

impl<'a, 'b> Mul<&'b Int> for &'a Int {
    type Output = Int;

    fn mul(self, other: &Int) -> Int {
        let mut self_clone = self.clone();
        self_clone *= other;
        self_clone
    }
}

impl<'a> Mul<Int> for &'a Int {
    type Output = Int;

    fn mul(self, mut other: Int) -> Int {
        other *= self;
        other
    }
}

impl<'a> Mul<&'a Int> for Int {
    type Output = Int;

    fn mul(mut self, other: &Int) -> Int {
        self *= other;
        self
    }
}

impl Mul<Int> for Int {
    type Output = Int;

    fn mul(mut self, other: Int) -> Int {
        self *= &other;
        self
    }
}

impl<'a> DivAssign<&'a Int> for Int {
    fn div_assign(&mut self, other: &Int) {
        assert!(*other != Int::from_str("0").unwrap());
        if self.sign == Sign::Zero {
            *self = Int::from(0);
        } else {
            self.magnitude /= &other.magnitude;
            if self.sign == other.sign && self.sign == Sign::Negative {
                self.sign = Sign::Positive;
            } else if self.sign != other.sign {
                if self.sign != Sign::Negative {
                    self.sign = Sign::Negative;
                }
            }
        }
    }
}

impl<'a, 'b> Div<&'b Int> for &'a Int {
    type Output = Int;

    fn div(self, other: &Int) -> Int {
        let mut self_clone = self.clone();
        self_clone /= other;
        self_clone
    }
}

impl<'a> Div<Int> for &'a Int {
    type Output = Int;

    fn div(self, mut other: Int) -> Int {
        other /= self;
        other
    }
}

impl<'a> Div<&'a Int> for Int {
    type Output = Int;

    fn div(mut self, other: &Int) -> Int {
        self /= other;
        self
    }
}

impl Div<Int> for Int {
    type Output = Int;

    fn div(mut self, other: Int) -> Int {
        self /= &other;
        self
    }
}

impl Ord for Int {
    fn cmp(&self, rhs: &Int) -> Ordering {
        if self.sign == Sign::Positive {
            if rhs.sign == Sign::Negative || rhs.sign == Sign::Zero {
                Ordering::Greater
            } else {
                assert!(rhs.sign == Sign::Positive);
                self.magnitude.cmp(&rhs.magnitude)
            }
        } else if self.sign == Sign::Negative {
            if rhs.sign == Sign::Positive || rhs.sign == Sign::Zero {
                Ordering::Less
            } else {
                assert!(rhs.sign == Sign::Negative);
                if self.magnitude == rhs.magnitude {
                    Ordering::Equal
                } else if self.magnitude < rhs.magnitude {
                    Ordering::Greater
                } else {
                    assert!(self.magnitude > rhs.magnitude);
                    Ordering::Less
                }
            }
        } else {
            assert!(self.sign == Sign::Zero);
            if rhs.sign == Sign::Zero {
                Ordering::Equal
            } else if rhs.sign == Sign::Positive {
                Ordering::Less
            } else {
                assert!(rhs.sign == Sign::Negative);
                Ordering::Greater
            }
        }
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq<i32> for Int {
    fn eq(&self, other: &i32) -> bool {
        match self.sign {
            Sign::Zero => *other == 0,
            Sign::Positive => *other > 0 && self.magnitude == abs(*other),
            Sign::Negative => *other < 0 && self.magnitude == abs(*other),
        }
    }
}

impl PartialEq<Int> for i32 {
    fn eq(&self, other: &Int) -> bool {
        other == self
    }
}

impl PartialOrd<i32> for Int {
    fn partial_cmp(&self, other: &i32) -> Option<Ordering> {
        match self.sign {
            Sign::Zero => 0i32.partial_cmp(other),
            Sign::Positive => {
                if *other <= 0 {
                    Some(Ordering::Greater)
                } else {
                    self.magnitude.partial_cmp(&abs(*other))
                }
            }
            Sign::Negative => {
                if *other >= 0 {
                    Some(Ordering::Less)
                } else {
                    Some(self.magnitude.partial_cmp(&abs(*other)).unwrap().reverse())
                }
            }
        }
    }
}

impl PartialOrd<Int> for i32 {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(other.partial_cmp(self).unwrap().reverse())
    }
}

/// Returns the absolute value of the given number.
///
/// # Examples
///
/// ```
/// let negative_five = -5;
///
/// assert_eq!(5, rust_number::int::abs(negative_five));
/// ```
pub fn abs(x: i32) -> u32 {
    if x < 0 {
        if x == i32::min_value() {
            0x80000000u32
        } else {
            -x as u32
        }
    } else {
        x as u32
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_from_u32() {
        let two = Int {
            magnitude: UInt::from(2),
            sign: Sign::Positive,
        };
        let negative_hundred = Int {
            magnitude: UInt::from(100),
            sign: Sign::Negative,
        };
        assert_eq!(two, Int::from(2));
        assert_eq!(negative_hundred, Int::from(-100));
    }

    #[test]
    fn from_str_test() {
        assert_eq!(Int::from(1), Int::from_str("1").unwrap());
        assert_eq!(Int::from(0), Int::from_str("0").unwrap());
        assert_eq!(Int::from(-1), Int::from_str("-1").unwrap());
    }

    #[test]
    fn add_assign_test() {
        let mut a = Int::from(0);
        a += &Int::from(0);
        assert_eq!(a, Int::from(0),);
        let mut b = Int::from(3);
        b += &Int::from(-2);
        assert_eq!(b, Int::from(1),);
    }

    #[test]
    fn add_test() {
        let zero = Int::from(0);
        let one = Int::from(1);
        let two = Int::from(2);
        let three = Int::from(3);
        let negative_two = Int::from(-2);
        let negative_one = Int::from(-1);
        let negative_three = Int::from(-3);
        assert_eq!(&zero + &zero, zero);
        assert_eq!(&zero + &one, one);
        assert_eq!(&zero + &negative_one, negative_one);
        assert_eq!(&one + &zero, one);
        assert_eq!(&one + &one, two);
        assert_eq!(&one + &two, three);
        assert_eq!(&two + &one, three);
        assert_eq!(&one + &negative_one, zero);
        assert_eq!(&one + &negative_two, negative_one);
        assert_eq!(&two + &negative_one, one);
        assert_eq!(&negative_one + &zero, negative_one);
        assert_eq!(&negative_one + &one, zero);
        assert_eq!(&negative_one + &two, one);
        assert_eq!(&negative_two + &one, negative_one);
        assert_eq!(&negative_one + &negative_one, negative_two);
        assert_eq!(&negative_one + &negative_two, negative_three);
        assert_eq!(&negative_two + &negative_one, negative_three);
    }
    #[test]
    fn sub_test() {
        let zero = Int::from(0);
        let one = Int::from(1);
        let two = Int::from(2);
        let three = Int::from(3);
        let negative_two = Int::from(-2);
        let negative_one = Int::from(-1);
        let negative_three = Int::from(-3);
        assert_eq!(&zero - &zero, zero);
        assert_eq!(&zero - &one, negative_one);
        assert_eq!(&zero - &negative_one, one);
        assert_eq!(&one - &zero, one);
        assert_eq!(&one - &one, zero);
        assert_eq!(&one - &two, negative_one);
        assert_eq!(&two - &one, one);
        assert_eq!(&one - &negative_one, two);
        assert_eq!(&one - &negative_two, three);
        assert_eq!(&two - &negative_one, three);
        assert_eq!(&negative_one - &zero, negative_one);
        assert_eq!(&negative_one - &one, negative_two);
        assert_eq!(&negative_one - &two, negative_three);
        assert_eq!(&negative_two - &one, negative_three);
        assert_eq!(&negative_one - &negative_one, zero);
        assert_eq!(&negative_one - &negative_two, one);
        assert_eq!(&negative_two - &negative_one, negative_one);
    }

    #[test]
    fn neg_test() {
        let zero = Int::from(0);
        let one = Int::from(1);
        assert_eq!(zero, -&zero);
        assert_eq!(-one, Int::from(-1));
    }

    #[test]
    fn mul_small_test() {
        let negative_two = Int::from(-2);
        let negative_one = Int::from(-1);
        let zero = Int::from(0);
        let one = Int::from(1);
        let two = Int::from(2);
        assert_eq!(&negative_two * &one, negative_two);
        assert_eq!(&negative_two * &zero, zero);
        assert_eq!(&zero * &zero, zero);
        assert_eq!(&negative_one * &negative_one, one);
        assert_eq!(&one * &one, one);
        assert_eq!(&one * &two, two);
    }

    #[test]
    fn mul_large_test() {
        let a = Int::from_str("4294967295").unwrap();
        let b = Int::from_str("4294967296").unwrap();
        let c = Int::from_str("18446744069414584320").unwrap();
        assert_eq!(&a * &b, c);

        let d = Int::from_str("-4294967295").unwrap();
        let e = Int::from_str("4294967296").unwrap();
        let f = Int::from_str("-18446744069414584320").unwrap();
        assert_eq!(&d * &e, f);

        let zero = Int::from_str("0").unwrap();
        assert_eq!(&zero * &f, zero);
    }

    #[test]
    fn div_small_test() {
        let negative_two = Int::from(-2);
        let negative_one = Int::from(-1);
        let zero = Int::from(0);
        let one = Int::from(1);
        let two = Int::from(2);
        assert_eq!(&negative_two / &one, negative_two);
        assert_eq!(&zero / &negative_two, zero);
        assert_eq!(&negative_one / &negative_one, one);
        assert_eq!(&one / &one, one);
        assert_eq!(&two / &two, one);
    }

    #[test]
    fn div_large_test() {
        let zero = Int::from_str("0").unwrap();
        let a =
            Int::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let b =
            Int::from_str("6277101735386680763835789423207666416120802188576398770190").unwrap();
        let c = Int::from_str(
            "3940200619639447921227904010014361380531132344942535809894852023048099751633866737197\
             3139355530553882773662438785150",
        ).unwrap();
        assert_eq!(&zero / &c, zero);
        assert_eq!(&c / &a, b);
        assert_eq!((&c + Int::from(1)) / &a, b);
        assert_eq!((&c - Int::from(1)) / &a, &b - Int::from(1));
    }

    #[test]
    fn ord_test() {
        let one = Int::from(1);
        let zero = Int::from(0);
        let negative_one = Int::from(-1);
        let a =
            Int::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let b =
            Int::from_str("-6277101735386680763835789423207666416120802188576398770190").unwrap();

        assert!(one > zero);
        assert!(one > negative_one);
        assert!(one == one);
        assert!(zero < one);
        assert!(zero == zero);
        assert!(zero > negative_one);
        assert!(negative_one < one);
        assert!(negative_one < zero);
        assert!(negative_one == negative_one);
        assert!(a > b);
        assert!(b < a);
        assert!(a > zero);
        assert!(b < zero);
        assert!(zero < a);
        assert!(zero > b);
    }

    #[test]
    fn partialeq_test() {
        let zero = Int::from(0);
        let one = Int::from(1);
        let negative_one = Int::from(-1);
        let c = Int::from_str("4294967296").unwrap();

        assert!(zero == 0);
        assert!(one == 1);
        assert!(negative_one == -1);
        assert!(&one == &Int::from(1));
        assert!(zero != 1);
        assert!(0 != c);
        assert!(c != 0);
    }

    #[test]
    fn partial_ord_i32_test() {
        let zero = Int::from(0);
        let one = Int::from(1);
        let negative_one = Int::from(-1);
        let a =
            Int::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let b =
            Int::from_str("-6277101735386680763835789423207666416120802188576398770190").unwrap();

        assert!(zero < 1);
        assert!(zero > -1);
        assert!(one > 0);
        assert!(one > -1);
        assert!(negative_one < 0);
        assert!(negative_one < 1);
        assert!(1 > zero);
        assert!(a > 1);
        assert!(1 < a);
        assert!(b < -1);
        assert!(-1 > b);
        assert!(zero <= 0);
        assert!(zero <= 1);
    }
}
