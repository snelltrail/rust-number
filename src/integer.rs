use std::cmp::max;
use std::cmp::Ordering;
use std::ops::AddAssign;
use std::ops::Add;

#[derive(Debug, Eq, PartialEq)]

pub struct Int {
    is_negative: bool,
    digits: Vec<u32>,
}

impl Int {
    pub fn new(is_negative: bool, digits: Vec<u32>) -> Int {
        Int {
            is_negative,
            digits,
        }
    }

    pub fn new_from_i32(num: i32) -> Int {
        Int {
            is_negative: num < 0,
            digits: vec![abs(num)],
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
}

impl AddAssign for Int {
    fn add_assign(&mut self, other: Int) {
        if self.is_negative || other.is_negative {
            unimplemented!()
        }
        self.add_ignoring_sign(&other);
    }
}

impl Add for Int {
    type Output = Int;

    fn add(self, other: Int) -> Int {
        let mut res = Int {
            is_negative: self.is_negative,
            digits: self.digits,
        };
        res += other;
        return res;
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
            match less_in_magnitude(self, rhs) {
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

fn less_in_magnitude(lhs: &Int, rhs: &Int) -> Ordering {
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
        let mut a = Int::new_from_i32(0);
        a += Int::new_from_i32(0);
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
        let a = Int::new_from_i32(0) + Int::new_from_i32(0);
        assert_eq!(
            a,
            Int {
                is_negative: false,
                digits: vec![0],
            }
        );
        let b = Int::new_from_i32(2) + Int::new_from_i32(3);
        assert_eq!(
            b,
            Int {
                is_negative: false,
                digits: vec![5],
            }
        );
        let c = Int::new_from_i32(i32::max_value()) + Int::new_from_i32(i32::max_value())
            + Int::new_from_i32(i32::max_value());
        assert_eq!(
            c,
            Int {
                is_negative: false,
                digits: vec![2147483645, 1],
            }
        );
    }
}
