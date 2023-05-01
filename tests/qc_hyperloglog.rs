use std::collections::{HashMap, HashSet};

use buildx_pdsa::cardinality::hyperloglog::HyperLogLog;
use quickcheck::Arbitrary;
use rand::Rng;

#[derive(Clone, Debug)]
struct HyperLogLogInput {
    error_rate: f64,
    data: Vec<u32>,
}

#[quickcheck_macros::quickcheck]
fn quickcheck_hyperloglog(input: HyperLogLogInput) {
    if input.data.is_empty() {
        return;
    }

    let register_bit_count_b = (1.04 / input.error_rate).powi(2).ln().ceil() as usize;
    let num_buckets_m = 1 << register_bit_count_b;
    if !(num_buckets_m >= 16 && num_buckets_m <= 65536) {
        return;
    }

    dbg!(&input);
    let mut hll = HyperLogLog::<u32>::new(input.error_rate).unwrap();
    input.data.iter().for_each(|item| hll.insert(item));
    let actual_count = input.data.iter().collect::<HashSet<_>>().iter().count();
    let estimated_count = hll.estimate();

    let error = ((actual_count as f64 - estimated_count as f64) / (actual_count as f64)).abs();

    println!("Num buckets {}", hll.num_buckets_m());
    let estimated_error = 1.04 / (2.0_f64.powf(hll.num_buckets_m() as f64)).sqrt();

    println!("Actual count : {actual_count}. Estimated count is {estimated_count}");
    println!("Actual Error is : {error}. Estimated error is {estimated_error}");
    assert!(error >= 0.0);
    assert!(error <= estimated_error)
}

impl Arbitrary for HyperLogLogInput {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let error_rate = rand::thread_rng().gen_range(0.01..0.5);
        let data = Vec::<u32>::arbitrary(g);

        HyperLogLogInput { error_rate, data }
    }
}
