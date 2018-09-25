#![feature(test)]

extern crate test;

pub mod integer;
pub mod uint;

use std::str::FromStr;
use uint::UInt;

#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;

    #[bench]
    fn bench_from_str(b: &mut Bencher) {
        b.iter(|| {
            let _a = UInt::from_str("10715086071862673209484250490600018105614048117055336074437503883703510511249361224931983788156958581275946729175531468251871452856923140435984577574698574803934567774824230985421074605062371141877954182153046474983581941267398767559165543946077062914571196477686542167660429831652624386837205668069673").unwrap();
        });
    }

    #[bench]
    fn bench_add(b: &mut Bencher) {
        let x =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let y =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770190").unwrap();
        b.iter(|| {
            let _c = &x + &y;
        });
    }

    #[bench]
    fn bench_sub(b: &mut Bencher) {
        let x =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let y =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770190").unwrap();
        b.iter(|| {
            let _z = &y - &x;
        });
    }

    #[bench]
    fn bench_mul(b: &mut Bencher) {
        let x =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770185").unwrap();
        let y =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770190").unwrap();
        b.iter(|| {
            let _z = &y * &x;
        });
    }

    #[bench]
    fn bench_div(b: &mut Bencher) {
        let x =
            UInt::from_str("6277101735386680763835789423207666416120802188576398770190").unwrap();
        let y = UInt::from_str("3940200619639447921227904010014361380531132344942535809894852023048099751633866737197313935553055388277366243878515").unwrap();
        b.iter(|| {
            let _z = &y / &x;
        });
    }
}
