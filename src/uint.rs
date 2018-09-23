use std::cmp::{max, Ordering};
use std::num::ParseIntError;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::str::FromStr;

#[derive(Debug, Eq, PartialEq, Clone)]

pub struct UInt {
    digits: Vec<u32>,
}

impl From<u32> for UInt {
    fn from(num: u32) -> Self {
        UInt { digits: vec![num] }
    }
}

impl FromStr for UInt {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut res = UInt::from(0);
        for c in s.chars() {
            res *= 10;
            res += c.to_digit(10).unwrap();
        }

        Ok(res)
    }
}

impl UInt {
    pub fn new(digits: Vec<u32>) -> UInt {
        UInt { digits }
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

    fn shift_by(&mut self, i: usize) {
        if *self != UInt::from(0) {
            for _ in 0..i {
                // TODO: This can be implemented more efficiently by adding zeros to the
                // end and rotating.
                self.digits.insert(0, 0);
            }
        }
    }

    fn divide_by_2(&mut self) {
        if self.digits.len() == 1 {
            self.digits[0] >>= 1;
        } else {
            for i in 0..self.digits.len() - 1 {
                self.digits[i] >>= 1;
                let lsb = self.digits[i + 1] & 1u32;
                self.digits[i] |= lsb << 31;
            }
            let last = self.digits.len() - 1;
            self.digits[last] >>= 1;
            self.remove_leading_zeros();
        }
    }
}

impl<'a> AddAssign<&'a UInt> for UInt {
    fn add_assign(&mut self, other: &UInt) {
        let mut carry: u32 = 0;
        let mut i = 0;
        while i < max(self.digits.len(), other.digits.len()) || carry != 0 {
            // Make sure that self.digits is big enough to store the next digit
            if i >= self.digits.len() {
                self.digits.push(0);
                assert_eq!(i, self.digits.len() - 1);
            }

            let (next_digit, next_carry) = add_with_carry(
                self.digits[i],
                if i < other.digits.len() {
                    other.digits[i]
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

impl<'a, 'b> Add<&'b UInt> for &'a UInt {
    type Output = UInt;

    fn add(self, other: &UInt) -> UInt {
        let mut self_clone = self.clone();
        self_clone += other;
        self_clone
    }
}

impl<'a> Add<UInt> for &'a UInt {
    type Output = UInt;

    fn add(self, mut other: UInt) -> UInt {
        other += self;
        other
    }
}

impl<'a> Add<&'a UInt> for UInt {
    type Output = UInt;

    fn add(mut self, other: &UInt) -> UInt {
        self += other;
        self
    }
}

impl Add<UInt> for UInt {
    type Output = UInt;

    fn add(mut self, other: UInt) -> UInt {
        self += &other;
        self
    }
}

impl AddAssign<u32> for UInt {
    fn add_assign(&mut self, other: u32) {
        // TODO Make this not use heap allocation
        let other = UInt::from(other);
        *self += &other;
    }
}

impl Add<u32> for UInt {
    type Output = UInt;

    fn add(mut self, other: u32) -> UInt {
        self += other;
        self
    }
}

impl<'a> Add<u32> for &'a UInt {
    type Output = UInt;

    fn add(self, other: u32) -> UInt {
        self.clone() + other
    }
}

impl Add<UInt> for u32 {
    type Output = UInt;

    fn add(self, other: UInt) -> UInt {
        other + self
    }
}

impl<'a> Add<&'a UInt> for u32 {
    type Output = UInt;

    fn add(self, other: &UInt) -> UInt {
        other + self
    }
}

// //TODO: Implement Sub using SubAssign to avoid unnecessary copies
impl<'a, 'b> Sub<&'b UInt> for &'a UInt {
    type Output = UInt;

    fn sub(self, other: &UInt) -> UInt {
        let mut self_clone = self.clone();
        self_clone -= other;
        self_clone
    }
}

impl<'a> Sub<UInt> for &'a UInt {
    type Output = UInt;

    fn sub(self, other: UInt) -> UInt {
        let mut self_clone = self.clone();
        self_clone -= &other;
        self_clone
    }
}

impl<'a> Sub<&'a UInt> for UInt {
    type Output = UInt;

    fn sub(mut self, other: &UInt) -> UInt {
        self -= other;
        self
    }
}

impl Sub<UInt> for UInt {
    type Output = UInt;

    fn sub(mut self, other: UInt) -> UInt {
        self -= &other;
        self
    }
}

impl<'a> SubAssign<&'a UInt> for UInt {
    fn sub_assign(&mut self, other: &UInt) {
        assert!(*self >= *other);
        for i in 0..self.digits.len() {
            let curr_rhs_digit = match other.digits.get(i) {
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
}

impl SubAssign<u32> for UInt {
    fn sub_assign(&mut self, other: u32) {
        let other = UInt::from(other);
        *self -= &other;
    }
}

impl Sub<u32> for UInt {
    type Output = UInt;

    fn sub(mut self, other: u32) -> UInt {
        self -= other;
        self
    }
}

impl<'a> Sub<u32> for &'a UInt {
    type Output = UInt;

    fn sub(self, other: u32) -> UInt {
        self.clone() - other
    }
}

impl Sub<UInt> for u32 {
    type Output = UInt;

    fn sub(self, other: UInt) -> UInt {
        other - self
    }
}

impl<'a> Sub<&'a UInt> for u32 {
    type Output = UInt;

    fn sub(self, other: &UInt) -> UInt {
        other - self
    }
}

impl<'a> MulAssign<&'a UInt> for UInt {
    fn mul_assign(&mut self, other: &UInt) {
        let mut res = UInt::from(0);
        for i in 0..other.digits.len() {
            let mut single_multiplication = multiply(self, other.digits[i]);
            single_multiplication.shift_by(i);
            res += &single_multiplication;
        }
        res.remove_leading_zeros();
        *self = res;
    }
}

impl<'a, 'b> Mul<&'b UInt> for &'a UInt {
    type Output = UInt;

    fn mul(self, other: &UInt) -> UInt {
        let mut self_clone = self.clone();
        self_clone *= other;
        self_clone
    }
}

impl<'a> Mul<UInt> for &'a UInt {
    type Output = UInt;

    fn mul(self, mut other: UInt) -> UInt {
        other *= self;
        other
    }
}

impl<'a> Mul<&'a UInt> for UInt {
    type Output = UInt;

    fn mul(mut self, other: &UInt) -> UInt {
        self *= other;
        self
    }
}

impl Mul<UInt> for UInt {
    type Output = UInt;

    fn mul(mut self, other: UInt) -> UInt {
        self *= &other;
        self
    }
}

impl MulAssign<u32> for UInt {
    fn mul_assign(&mut self, other: u32) {
        let other = UInt::from(other);
        *self *= &other;
    }
}

impl Mul<u32> for UInt {
    type Output = UInt;

    fn mul(mut self, other: u32) -> UInt {
        self *= other;
        self
    }
}

impl<'a> Mul<u32> for &'a UInt {
    type Output = UInt;

    fn mul(self, other: u32) -> UInt {
        self.clone() * other
    }
}

impl Mul<UInt> for u32 {
    type Output = UInt;

    fn mul(self, other: UInt) -> UInt {
        other * self
    }
}

impl<'a> Mul<&'a UInt> for u32 {
    type Output = UInt;

    fn mul(self, other: &UInt) -> UInt {
        other * self
    }
}

impl<'a> DivAssign<&'a UInt> for UInt {
    fn div_assign(&mut self, other: &UInt) {
        assert!(*other != UInt::from(0));
        if *self < *other {
            *self = UInt::from(0);
        } else {
            let mut lo = UInt::from(0);
            let mut hi = UInt::from(1);
            hi.shift_by(self.digits.len() - other.digits.len() + 1);
            let mut res = UInt::from(0);
            while lo <= hi {
                let mut mid = &lo + &hi;
                mid.divide_by_2();
                let mid_times_denom = &mid * other;
                if mid_times_denom == *self {
                    *self = mid;
                    return;
                } else if *self < mid_times_denom {
                    hi = mid - UInt::from(1);
                } else {
                    lo = &mid + UInt::from(1);
                    res = mid;
                }
            }
            *self = res;
        }
    }
}

impl<'a, 'b> Div<&'b UInt> for &'a UInt {
    type Output = UInt;

    fn div(self, other: &UInt) -> UInt {
        let mut self_clone = self.clone();
        self_clone /= other;
        self_clone
    }
}

impl<'a> Div<UInt> for &'a UInt {
    type Output = UInt;

    fn div(self, mut other: UInt) -> UInt {
        other /= self;
        other
    }
}

impl<'a> Div<&'a UInt> for UInt {
    type Output = UInt;

    fn div(mut self, other: &UInt) -> UInt {
        self /= other;
        self
    }
}

impl Div<UInt> for UInt {
    type Output = UInt;

    fn div(mut self, other: UInt) -> UInt {
        self /= &other;
        self
    }
}

impl DivAssign<u32> for UInt {
    fn div_assign(&mut self, other: u32) {
        let other = UInt::from(other);
        *self /= &other;
    }
}

impl Div<u32> for UInt {
    type Output = UInt;

    fn div(mut self, other: u32) -> UInt {
        self /= other;
        self
    }
}

impl<'a> Div<u32> for &'a UInt {
    type Output = UInt;

    fn div(self, other: u32) -> UInt {
        self.clone() / other
    }
}

impl Div<UInt> for u32 {
    type Output = UInt;

    fn div(self, other: UInt) -> UInt {
        other / self
    }
}

impl<'a> Div<&'a UInt> for u32 {
    type Output = UInt;

    fn div(self, other: &UInt) -> UInt {
        other / self
    }
}

impl PartialOrd for UInt {
    fn partial_cmp(&self, other: &UInt) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for UInt {
    fn cmp(&self, rhs: &UInt) -> Ordering {
        if self.digits.len() < rhs.digits.len() {
            Ordering::Less
        } else if self.digits.len() > rhs.digits.len() {
            Ordering::Greater
        } else {
            for i in (0..self.digits.len()).rev() {
                if self.digits[i] < rhs.digits[i] {
                    return Ordering::Less;
                } else if self.digits[i] > rhs.digits[i] {
                    return Ordering::Greater;
                }
            }
            Ordering::Equal
        }
    }
}

fn multiply(lhs: &UInt, rhs: u32) -> UInt {
    let mut res = UInt { digits: vec![] };
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

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_from_u32() {
        let two = UInt { digits: vec![2] };
        let hundred = UInt { digits: vec![100] };
        assert_eq!(two, UInt::from(2));
        assert_eq!(hundred, UInt::from(100));
    }

    #[test]
    fn test_from_str() {
        let two = UInt::from_str("2").unwrap();
        let hundred = UInt::from_str("100").unwrap();
        assert_eq!(two, UInt::from(2));
        assert_eq!(hundred, UInt::from(100));
        let a = UInt::from_str("10715086071862673209484250490600018105614048117055336074437503883703510511249361224931983788156958581275946729175531468251871452856923140435984577574698574803934567774824230985421074605062371141877954182153046474983581941267398767559165543946077062914571196477686542167660429831652624386837205668069673").unwrap();
        assert_eq!(
            a,
            UInt {
                digits: vec![
                    297, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 256
                ]
            }
        );
    }

    #[test]
    fn ord_test() {
        let zero = UInt::from(0);
        let one = UInt::from(1);
        let hundred = UInt::from(100);
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
        let mut a = UInt::from(0);
        a += &UInt::from(0);
        assert_eq!(a, UInt::from(0));
    }

    #[test]
    fn add_with_u32_test() {
        let mut a = UInt::from(0);
        a += 0;
        a = &a + 0;
        a = 0 + &a;
        assert_eq!(a, UInt::from(0));
    }

    #[test]
    fn add_test() {
        let zero = UInt::from(0);
        let one = UInt::from(1);
        let two = UInt::from(2);
        assert_eq!(&zero + &zero, zero);
        assert_eq!(UInt::from(2) + UInt::from(2), UInt::from(4));
        assert_eq!(&one + &one, two);

        let a = UInt::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let b = UInt::from_str("6277101735386680763835789423207666416120802188576398770190").unwrap();
        let c = UInt::from_str("12554203470773361527671578846415332832241604377152797540375").unwrap();
        assert_eq!(&a + UInt::from(5), b);
        assert_eq!(&a + &b, c);

        let d = UInt::from(4294967295u32);
        let e = UInt::from_str("4294967296").unwrap();
        assert_eq!(e, d + UInt::from(1));
    }

    #[test]
    fn sub_test() {
        let a = UInt::from(0) - UInt::from(0);
        assert_eq!(a, UInt::from(0));
        let b = UInt::from(3) - UInt::from(2);
        assert_eq!(b, UInt::from(1));
        let mut c = UInt::from(i32::max_value() as u32)
            + UInt::from(i32::max_value() as u32)
            + UInt::from(i32::max_value() as u32);
        c -= &UInt::from(1);
        assert_eq!(
            c,
            UInt::from_str("6442450940").unwrap()
            );
    }

    #[test]
    fn sub_with_u32_test() {
        let mut a = UInt::from(0);
        a -= 0;
        a = &a - 0;
        a = 0 - &a;
        assert_eq!(a, UInt::from(0));
    }

    #[test]
    fn mul_small_test() {
        let zero = UInt::from(0);
        let one = UInt::from(1);
        let two = UInt::from(2);
        assert_eq!(&zero * &zero, zero);
        assert_eq!(&one * &one, one);
        assert_eq!(&one * &two, two);
    }

    #[test]
    fn mul_large_test() {
        let a = UInt::from(4294967295u32);
        let b = UInt::from_str("4294967296").unwrap();
        let c = UInt::from_str("18446744069414584320").unwrap();
        assert_eq!(a * b, c);

        let d = UInt::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let e = UInt::from_str("6277101735386680763835789423207666416120802188576398770190").unwrap();
        let f = UInt::from_str("39402006196394479212279040100143613805311323449425358098948520230480997516338667371973139355530553882773662438785150").unwrap();
        assert_eq!(&d * e, f);
        assert_eq!(d * UInt::from(0), UInt::from(0));
    }

    #[test]
    fn mul_with_u32_test() {
        let mut a = UInt::from(0);
        a *= 0;
        a = &a * 0;
        a = 0 * &a;
        assert_eq!(a, UInt::from(0));
    }

    #[test]
    fn divide_by_2_test() {
        let mut a = UInt::from_str("4294967296").unwrap();
        let b = UInt::from(2147483648u32);
        a.divide_by_2();
        assert_eq!(a, b);
    }

    #[test]
    fn div_small_test() {
        let zero = UInt::from(0);
        let one = UInt::from(1);
        let two = UInt::from(2);
        assert_eq!(&zero / &one, zero);
        assert_eq!(&one / &one, one);
        assert_eq!(&two / &two, one);
    }

    #[test]
    fn div_large_test() {
        let a = UInt::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let b = UInt::from_str("6277101735386680763835789423207666416120802188576398770190").unwrap();
        let c = UInt::from_str("39402006196394479212279040100143613805311323449425358098948520230480997516338667371973139355530553882773662438785150").unwrap();
        assert_eq!(&c / &a, b);
        assert_eq!((&c + UInt::from(1)) / &a, b);
        assert_eq!((&c - UInt::from(1)) / &a, &b - UInt::from(1));
    }

    #[test]
    fn div_with_u32_test() {
        let mut a = UInt::from(1);
        a /= 1;
        a = &a / 1;
        a = 1 / &a;
        assert_eq!(a, UInt::from(1));
    }
}
