#![feature(test)]

extern crate rand;
extern crate test;

pub mod algorithm;
pub mod int;
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
            let _a = UInt::from_str(
                "107150860718626732094842504906000181056140481170553360744375038837035105112493612\
                 249319837881569585812759467291755314682518714528569231404359845775746985748039345\
                 677748242309854210746050623711418779541821530464749835819412673987675591655439460\
                 77062914571196477686542167660429831652624386837205668069673",
            ).unwrap();
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
        let y = UInt::from_str(
            "3940200619639447921227904010014361380531132344942535809894852023048099751633866737197\
             313935553055388277366243878515",
        ).unwrap();
        b.iter(|| {
            let _z = &y / &x;
        });
    }
}
