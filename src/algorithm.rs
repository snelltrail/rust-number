use std::mem::swap;
use uint::UInt;

pub fn gcd(x: &UInt, y: &UInt) -> UInt {
    let mut a = x.clone();
    let mut b = y.clone();
    while b != 0 {
        a %= &b;
        swap(&mut a, &mut b);
    }
    a
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_gcd() {
        let x = UInt::from(14175);
        let y = UInt::from(756315);
        let ans = UInt::from(315);
        assert_eq!(gcd(&x, &y), ans);
        assert_eq!(gcd(&y, &x), ans);
        assert_eq!(gcd(&ans, &UInt::from(1)), UInt::from(1));
    }
}
