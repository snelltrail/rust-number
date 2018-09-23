#![feature(test)]

extern crate test;

pub mod integer;
pub mod uint;

pub fn add_two(a: i32) -> i32 {
    a + 2
}

#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;

    #[bench]
    fn bench_add_two(b: &mut Bencher) {
        b.iter(|| {
            let mut a = uint::UInt::from(450);
            a *= &a.clone();
        });
    }
}
