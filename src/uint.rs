use std::cmp::{max, min, Ordering};
use std::num::ParseIntError;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign};
use std::str::FromStr;

#[derive(Debug, Eq, PartialEq, Clone)]

/// A UInt is an arbitrary precision unsigned integer.
///
/// It is represented  internally as a `Vec<u32>`. Where each element of the
/// vector is a digit base 2^32 and the first element is the least significant
/// digit. So `[3, 4, 5]` represents `5*(2^32)^2 + 4*2^32 + 3 =
/// 92233720385727627267`.
///
/// # Example
///
/// ```
/// // You can create a UInt from a u32 or a string slice.
/// use rust_number::uint::UInt;
/// use std::str::FromStr;
/// let one = UInt::from(1);
/// let x = UInt::from_str("10987654321").unwrap();
///
/// // You can add, subtract, multiply and divide UInts, provided the result is
/// // nonnegative.
/// let y = UInt::from(1) + UInt::from(2) - UInt::from(1) * UInt::from(2) / UInt::from(1);
///
/// // Elementary operations work with both `&Int` or and `Int`. In
/// // the example below the multiply function takes ownership of `x`, and
/// // takes a reference to `one`. This is more efficient than `let y = &x * &one`
/// // as `x`'s memory can be reused for the result. The disadvantage is that `x`
/// // can not be used after this operation.
/// let y = x * &one;
/// ```
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
        for i in (0..s.len()).step_by(9) {
            res *= if i + 9 < s.len() {
                1000000000u32
            } else {
                let mut pow_of_ten = 1u32;
                for _ in 0..s.len() - i {
                    pow_of_ten *= 10u32;
                }
                pow_of_ten
            };
            res += s[i..min(i + 9, s.len())].parse::<u32>().unwrap();
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

    fn num_bits(&self) -> usize {
        if self.is_zero() {
            0
        } else {
            (self.digits.len() - 1) * 32 + num_bits(*self.digits.last().unwrap())
        }
    }

    fn shift_digits_left(&mut self, i: u32) {
        if *self != UInt::from(0) {
            self.digits.reserve(i as usize);
            for _ in 0..i {
                self.digits.push(0);
            }
            self.digits.rotate_right(i as usize);
        }
    }

    fn shift_x_bits_left(&mut self, x: i32) {
        if x != 0 {
            let mut prev_msb = 0u32;
            for i in 0..self.digits.len() {
                let curr_msb = self.digits[i] >> (32 - x);
                self.digits[i] <<= x;
                self.digits[i] |= prev_msb;
                prev_msb = curr_msb;
            }
            if prev_msb != 0 {
                self.digits.push(prev_msb);
            }
        }
    }

    fn shift_bits_left(&mut self, i: u32) {
        self.shift_digits_left(i >> 5);
        self.shift_x_bits_left((i & 0x1F) as i32);
    }

    fn set_bit(&mut self, i: u32) {
        let idx = (i >> 5) as usize;
        self.digits[idx] |= 1 << (i & 0x1F);
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

    pub fn is_zero(&self) -> bool {
        self.digits.len() == 1 && self.digits[0] == 0
    }

    pub fn set_zero(&mut self) {
        self.digits.clear();
        self.digits.push(0);
    }
}

impl<'a> AddAssign<&'a UInt> for UInt {
    fn add_assign(&mut self, other: &UInt) {
        let mut carry: u32 = 0;
        let mut i = 0;
        if self.digits.len() < other.digits.len() {
            let len_diff = other.digits.len() - self.digits.len();
            self.digits.reserve(len_diff);
        }
        while i < max(self.digits.len(), other.digits.len()) || carry != 0 {
            // Make sure that self.digits is big enough to store the next digit
            if i >= self.digits.len() {
                self.digits.push(0);
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
        res.digits.reserve(self.digits.len() + other.digits.len());
        for i in 0..other.digits.len() {
            let mut single_multiplication = multiply(self, other.digits[i]);
            single_multiplication.shift_digits_left(i as u32);
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
        assert!(!other.is_zero());
        if *self < *other {
            self.set_zero();
        } else {
            let mut set_bits = Vec::new();
            while *self >= *other {
                let i = divide_once(self, other);
                set_bits.push(i);
            }
            let mut res = UInt::from(1);
            res.shift_bits_left(*set_bits.first().unwrap());
            for i in &set_bits[1..] {
                res.set_bit(*i);
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

impl<'a> RemAssign<&'a UInt> for UInt {
    fn rem_assign(&mut self, other: &UInt) {
        let self_clone = self.clone();
        *self = &self_clone - other * (&self_clone / other)
    }
}

impl<'a, 'b> Rem<&'b UInt> for &'a UInt {
    type Output = UInt;

    fn rem(self, other: &UInt) -> UInt {
        let mut self_clone = self.clone();
        self_clone %= other;
        self_clone
    }
}

impl<'a> Rem<UInt> for &'a UInt {
    type Output = UInt;

    fn rem(self, mut other: UInt) -> UInt {
        other %= self;
        other
    }
}

impl<'a> Rem<&'a UInt> for UInt {
    type Output = UInt;

    fn rem(mut self, other: &UInt) -> UInt {
        self %= other;
        self
    }
}

impl Rem<UInt> for UInt {
    type Output = UInt;

    fn rem(mut self, other: UInt) -> UInt {
        self %= &other;
        self
    }
}

impl RemAssign<u32> for UInt {
    fn rem_assign(&mut self, other: u32) {
        let other = UInt::from(other);
        *self %= &other;
    }
}

impl Rem<u32> for UInt {
    type Output = UInt;

    fn rem(mut self, other: u32) -> UInt {
        self %= other;
        self
    }
}

impl<'a> Rem<u32> for &'a UInt {
    type Output = UInt;

    fn rem(self, other: u32) -> UInt {
        self.clone() % other
    }
}

impl Rem<UInt> for u32 {
    type Output = UInt;

    fn rem(self, other: UInt) -> UInt {
        other % self
    }
}

impl<'a> Rem<&'a UInt> for u32 {
    type Output = UInt;

    fn rem(self, other: &UInt) -> UInt {
        other % self
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
    res.digits.reserve(lhs.digits.len() + 1);
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

// Returns z where x = y*2^z + r and z is maximal and reassigns x = r.
fn divide_once(x: &mut UInt, y: &UInt) -> u32 {
    let shift = x.num_bits() as u32 - y.num_bits() as u32;
    let mut y_clone = y.clone();
    y_clone.shift_bits_left(shift);
    if y_clone <= *x {
        *x -= &y_clone;
        shift
    } else {
        y_clone.divide_by_2();
        *x -= &y_clone;
        shift - 1
    }
}

fn num_bits(x: u32) -> usize {
    for i in 0..32 {
        if x >> i == 0 {
            return i;
        }
    }
    return 32;
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
        let a = UInt::from_str(
            "1071508607186267320948425049060001810561404811705533607443750388370351051124936122493\
             1983788156958581275946729175531468251871452856923140435984577574698574803934567774824\
             2309854210746050623711418779541821530464749835819412673987675591655439460770629145711\
             96477686542167660429831652624386837205668069673",
        ).unwrap();
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
    fn is_zero_test() {
        let zero = UInt::from(0);
        let one = UInt::from(1);
        let x = UInt::from_str("4294967296").unwrap();
        assert!(zero.is_zero());
        assert!(!one.is_zero());
        assert!(!x.is_zero());
    }

    #[test]
    fn shift_one_test() {
        let mut x = UInt::from(1);
        let one = UInt::from(1);
        let mut y = UInt::from(1);
        let two = UInt::from(2);
        for i in 0..100 {
            assert_eq!(x.num_bits(), i + 1);
            let mut x_clone = one.clone();
            x_clone.shift_bits_left(i as u32);
            assert_eq!(x, x_clone);
            x.shift_bits_left(1);
            y *= &two;
            assert_eq!(x, y);
        }
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

        let a =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let b =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770190").unwrap();
        let c =
            UInt::from_str("12554203470773361527671578846415332832241604377152797540375").unwrap();
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
        assert_eq!(c, UInt::from_str("6442450940").unwrap());
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

        let d =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let e =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770190").unwrap();
        let f = UInt::from_str(
            "3940200619639447921227904010014361380531132344942535809894852023048099751633866737197\
             3139355530553882773662438785150",
        ).unwrap();
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
        let a =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let b =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770190").unwrap();
        let c = UInt::from_str(
            "3940200619639447921227904010014361380531132344942535809894852023048099751633866737197\
             3139355530553882773662438785150",
        ).unwrap();
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

    #[test]
    fn rem_large_test() {
        let a =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let b = UInt::from_str(
            "3940200619639447921227904010014361380531132344942535809894852023048099751633866737197\
             3139355530553882773662438785150",
        ).unwrap();
        assert_eq!(&b % &a, UInt::from(0));
        assert_eq!((&b + UInt::from(1)) % &a, UInt::from(1));
        assert_eq!((&b - UInt::from(1)) % &a, &a - UInt::from(1));
    }

    #[test]
    fn rem_with_u32_test() {
        let mut a = UInt::from(1);
        a = 1 / &a;
        a %= 1;
        a = &a / 1;
        assert_eq!(a, UInt::from(0));
    }
}
