use std::cmp::{max, Ordering};
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

#[derive(Debug, Eq, PartialEq, Clone)]

pub struct Int {
    is_negative: bool,
    digits: Vec<u32>,
}

impl From<i32> for Int {
    fn from(num: i32) -> Self {
        Int {
            is_negative: num < 0,
            digits: vec![abs(num)],
        }
    }
}

impl Int {
    pub fn new(is_negative: bool, digits: Vec<u32>) -> Int {
        Int {
            is_negative,
            digits,
        }
    }

    pub fn add_ignoring_sign(&mut self, rhs: &Int) {
        let mut carry: u32 = 0;
        let mut i = 0;
        while i < max(self.digits.len(), rhs.digits.len()) || carry != 0 {
            // Make sure that self.digits is big enough to store the next digit
            if i >= self.digits.len() {
                self.digits.push(0);
                assert_eq!(i, self.digits.len() - 1);
            }

            let (next_digit, next_carry) = add_with_carry(
                self.digits[i],
                if i < rhs.digits.len() {
                    rhs.digits[i]
                } else {
                    0
                },
                carry,
            );
            self.digits[i] = next_digit;
            carry = next_carry;
            i += 1;
        }
    }

    fn remove_leading_zeros(&mut self) {
        while self.digits.len() > 1 && *self.digits.last().unwrap() == 0u32 {
            self.digits.pop();
        }
    }

    fn borrow_from_neighbour(&mut self, neighbour: usize) {
        assert!(neighbour < self.digits.len());
        let mut curr = neighbour;
        while self.digits[curr] == 0 {
            self.digits[curr] = u32::max_value();
            curr += 1;
            assert!(curr < self.digits.len());
        }
        self.digits[curr] -= 1;
    }

    fn subtract_ignoring_sign(&mut self, rhs: &Int) {
        assert!(match compare_in_magnitude(self, rhs) {
            Ordering::Less => false,
            Ordering::Equal => true,
            Ordering::Greater => true,
        });
        for i in 0..self.digits.len() {
            let curr_rhs_digit = match rhs.digits.get(i) {
                Some(x) => x,
                None => &0u32,
            };
            if self.digits[i] < *curr_rhs_digit {
                self.borrow_from_neighbour(i + 1);
            }
            if *curr_rhs_digit <= self.digits[i] {
                // Check for underflow.
                self.digits[i] -= *curr_rhs_digit;
            } else {
                self.digits[i] = ((u32::max_value() - curr_rhs_digit) + self.digits[i]) + 1;
            }
        }
        self.remove_leading_zeros();
    }

    fn shift_by(&mut self, i: usize) {
        if *self != Int::from(0) {
            for _ in 0..i {
                // TODO: This can be implemented more efficiently by adding zeros to the
                // end and rotating.
                self.digits.insert(0, 0);
            }
        }
    }
}

impl<'a> AddAssign<&'a Int> for Int {
    fn add_assign(&mut self, other: &Int) {
        if !self.is_negative && !other.is_negative {
            // Both nonnegative.
            self.add_ignoring_sign(other);
        } else if self.is_negative && other.is_negative {
            // Both are negative.
            self.add_ignoring_sign(other);
        } else {
            // One is negative, one is positive.
            match compare_in_magnitude(self, other) {
                Ordering::Equal => {
                    *self = Int::from(0);
                }
                Ordering::Greater => {
                    self.subtract_ignoring_sign(other);
                }
                Ordering::Less => {
                    let mut temp = self.clone();
                    *self = other.clone();
                    self.subtract_ignoring_sign(&temp);
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

impl SubAssign for Int {
    fn sub_assign(&mut self, other: Int) {
        if self.is_negative || other.is_negative || match compare_in_magnitude(self, &other) {
            Ordering::Less => true,
            Ordering::Equal => false,
            Ordering::Greater => false,
        } {
            unimplemented!();
        }
        self.subtract_ignoring_sign(&other);
    }
}

impl Sub for Int {
    type Output = Int;

    fn sub(self, other: Int) -> Int {
        let mut res = Int {
            is_negative: self.is_negative,
            digits: self.digits,
        };
        res -= other;
        return res;
    }
}

impl<'a> MulAssign<&'a Int> for Int {
    fn mul_assign(&mut self, other: &Int) {
        let mut res = Int::from(0);
        for i in 0..other.digits.len() {
            let mut single_multiplication = multiply_ignoring_sign(self, other.digits[i]);
            single_multiplication.shift_by(i);
            res += &single_multiplication;
        }
        res.is_negative = self.is_negative ^ other.is_negative;
        if res.digits.len() == 1 && res.digits[0] == 0 {
            res.is_negative = false;
        }
        *self = res;
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

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Int {
    fn cmp(&self, rhs: &Int) -> Ordering {
        if self.is_negative && !rhs.is_negative {
            Ordering::Less
        } else if !self.is_negative && rhs.is_negative {
            Ordering::Greater
        } else {
            // Both numbers have the same sign.
            let both_negative = self.is_negative;
            match compare_in_magnitude(self, rhs) {
                Ordering::Less => if both_negative {
                    Ordering::Greater
                } else {
                    Ordering::Less
                },
                Ordering::Greater => if both_negative {
                    Ordering::Less
                } else {
                    Ordering::Greater
                },
                Ordering::Equal => Ordering::Equal,
            }
        }
    }
}

fn multiply_ignoring_sign(lhs: &Int, rhs: u32) -> Int {
    let mut res = Int {
        is_negative: false,
        digits: vec![],
    };
    let mut carry = 0u32;
    for i in 0..lhs.digits.len() {
        let (next_digit, next_carry) = multiply_with_carry(lhs.digits[i], rhs, carry);
        res.digits.push(next_digit);
        carry = next_carry;
    }

    if carry != 0 {
        res.digits.push(carry);
    }

    res
}

fn compare_in_magnitude(lhs: &Int, rhs: &Int) -> Ordering {
    if lhs.digits.len() < rhs.digits.len() {
        Ordering::Less
    } else if lhs.digits.len() > rhs.digits.len() {
        Ordering::Greater
    } else {
        for i in (0..lhs.digits.len()).rev() {
            if lhs.digits[i] < rhs.digits[i] {
                return Ordering::Less;
            } else if lhs.digits[i] > rhs.digits[i] {
                return Ordering::Greater;
            }
        }
        Ordering::Equal
    }
}

fn add_with_carry(x: u32, y: u32, carry: u32) -> (u32, u32) {
    assert!(carry == 1 || carry == 0);
    let big_x = x as u64;
    let big_y = y as u64;
    let big_carry = carry as u64;
    let result = big_x + big_y + big_carry;
    let sum = result as u32;
    let result_carry = (result >> 32) as u32;
    (sum, result_carry)
}

fn multiply_with_carry(x: u32, y: u32, carry: u32) -> (u32, u32) {
    let big_x = x as u64;
    let big_y = y as u64;
    let big_carry = carry as u64;
    let res = big_x * big_y + big_carry;
    let prod = res as u32;
    let res_carry = (res >> 32) as u32;
    (prod, res_carry)
}

/// Returns the absolute value of the given number.
///
/// # Examples
///
/// ```
/// let negative_five = -5;
///
/// assert_eq!(5, rust_number::integer::abs(negative_five));
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
            is_negative: false,
            digits: vec![2],
        };
        let negative_hundred = Int {
            is_negative: true,
            digits: vec![100],
        };
        assert_eq!(two, Int::from(2));
        assert_eq!(negative_hundred, Int::from(-100));
    }

    #[test]
    fn int_works() {
        assert_eq!(
            Int::new(true, vec![1, 2]),
            Int {
                is_negative: true,
                digits: vec![1, 2],
            }
        );
    }

    #[test]
    fn abs_test() {
        assert_eq!(abs(-2), 2);
        assert_eq!(abs(0), 0);
        assert_eq!(abs(i32::min_value()), i32::max_value() as u32 + 1);
    }

    #[test]
    fn ord_test() {
        let negative_hundred = Int {
            is_negative: true,
            digits: vec![100],
        };
        let negative_one = Int {
            is_negative: true,
            digits: vec![1],
        };
        let zero = Int {
            is_negative: false,
            digits: vec![0],
        };
        let one = Int {
            is_negative: false,
            digits: vec![1],
        };
        let hundred = Int {
            is_negative: false,
            digits: vec![100],
        };
        assert!(negative_hundred < negative_one);
        assert!(negative_one < zero);
        assert!(zero < one);
        assert!(one < hundred);
    }

    #[test]
    fn add_with_carry_test() {
        assert_eq!(add_with_carry(0, 0, 0), (0, 0));
        assert_eq!(add_with_carry(1, 1, 1), (3, 0));
        assert_eq!(
            add_with_carry(u32::max_value() - 1, 1, 0),
            (u32::max_value(), 0)
        );
        assert_eq!(
            add_with_carry(u32::max_value() - 1, 0, 1),
            (u32::max_value(), 0)
        );
        assert_eq!(add_with_carry(u32::max_value(), 1, 0), (0, 1));
        assert_eq!(add_with_carry(u32::max_value(), 0, 1), (0, 1));
        assert_eq!(add_with_carry(u32::max_value(), 11, 0), (10, 1));
    }

    #[test]
    fn add_assign_test() {
        let mut a = Int::from(0);
        a += &Int::from(0);
        assert_eq!(
            a,
            Int {
                is_negative: false,
                digits: vec![0],
            }
        );
    }

    #[test]
    fn add_test() {
        let negative_two = Int::from(-2);
        let negative_one = Int::from(-1);
        let zero = Int::from(0);
        let one = Int::from(1);
        let two = Int::from(2);
        assert_eq!(&negative_two + &one, negative_one);
        assert_eq!(&negative_two + &two, zero);
        assert_eq!(&zero + &zero, zero);
        assert_eq!(Int::from(2) + Int::from(-2), Int::from(0));
        assert_eq!(&one + &one, two);

        let a = Int {
            is_negative: false,
            digits: vec![9, 9, 1, 0, 0, 0, 1],
        };
        let minus_a = Int {
            is_negative: true,
            digits: vec![9, 9, 1, 0, 0, 0, 1],
        };
        let b = Int {
            is_negative: false,
            digits: vec![14, 9, 1, 0, 0, 0, 1],
        };
        let minus_b = Int {
            is_negative: true,
            digits: vec![14, 9, 1, 0, 0, 0, 1],
        };
        let c = Int {
            is_negative: false,
            digits: vec![23, 18, 2, 0, 0, 0, 2],
        };
        let minus_c = Int {
            is_negative: true,
            digits: vec![23, 18, 2, 0, 0, 0, 2],
        };
        assert_eq!(&a + &minus_a, zero);
        assert_eq!(&a + Int::from(5), b);
        assert_eq!(&a + &b, c);
        assert_eq!(&a + &minus_b, Int::from(-5));
        assert_eq!(&a + &minus_c, minus_b);

        let d = Int {
            is_negative: false,
            digits: vec![4294967295u32],
        };
        let e = Int {
            is_negative: false,
            digits: vec![0, 1],
        };
        assert_eq!(&e + &negative_one, d);
    }

    #[test]
    fn sub_test() {
        let a = Int::from(0) - Int::from(0);
        assert_eq!(
            a,
            Int {
                is_negative: false,
                digits: vec![0],
            }
        );
        let b = Int::from(3) - Int::from(2);
        assert_eq!(
            b,
            Int {
                is_negative: false,
                digits: vec![1],
            }
        );
        let mut c =
            Int::from(i32::max_value()) + Int::from(i32::max_value()) + Int::from(i32::max_value());
        c -= Int::from(1);
        assert_eq!(
            c,
            Int {
                is_negative: false,
                digits: vec![2147483644, 1],
            }
        );
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
        let a = Int {
            is_negative: false,
            digits: vec![4294967295u32],
        };
        let b = Int {
            is_negative: false,
            digits: vec![0, 1],
        };
        let c = Int {
            is_negative: false,
            digits: vec![0, 4294967295u32],
        };
        assert_eq!(a * b, c);

        let d = Int {
            is_negative: false,
            digits: vec![9, 9, 1, 0, 0, 0, 1],
        };
        let e = Int {
            is_negative: false,
            digits: vec![14, 9, 1, 0, 0, 0, 1],
        };
        let f = Int {
            is_negative: false,
            digits: vec![126, 207, 104, 18, 1, 0, 23, 18, 2, 0, 0, 0, 1],
        };
        assert_eq!(d * e, f);
    }
}
