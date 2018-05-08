#[derive(Debug, PartialEq)]

struct Int {
    is_negative: bool,
    digits: Vec<u32>,
}

impl Int {
    fn new(is_negative: bool, digits: Vec<u32>) -> Int {
        Int { is_negative, digits }
    }

    fn new_from_i32(num: i32) -> Int {
            Int { is_negative: num < 0, digits: vec![abs(num)] }
    }
}

/// Returns the absolute value of the given number.
///
/// # Examples
///
/// ```
/// let negative_five = -5;
///
/// assert_eq!(5, rust_number::abs(negative_five));
/// ```
pub fn abs(x: i32) -> u32 {
    if x < 0 {
        if x == i32::min_value() {
            0x80000000
        } else {
            -x as u32
        }
    } else {
        x as u32
    }
}

#[cfg(test)]
mod tests {
    use super::Int;
    use super::abs;
    #[test]
    fn int_works() {
        assert_eq!(Int::new(true,vec![1,2]), Int { is_negative: true, digits: vec![1,2] } );
    }

    #[test]
    fn abs_test() {
        assert_eq!(abs(-2), 2);
        assert_eq!(abs(0), 0);
        assert_eq!(abs(i32::min_value()), i32::max_value() as u32 + 1);
    }
}
