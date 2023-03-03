use buildx_pdsa::membership::bloom_filter::BloomFilter;
use quickcheck::Arbitrary;
use rand::Rng;

#[derive(Clone, Debug)]
struct BloomTestInput {
    num_items: usize,
    false_positive_rate: f64,
    data: Vec<u32>,
    not_present: Vec<u32>,
}

#[quickcheck_macros::quickcheck]
fn quickcheck_bloom_filter(input: BloomTestInput) {
    dbg!(&input);
    let mut bloom_filter =
        BloomFilter::<u32>::new(input.num_items, input.false_positive_rate).unwrap();
    input.data.iter().for_each(|item| bloom_filter.insert(item));
    assert!(input.data.iter().all(|item| bloom_filter.contains(item)));
    let mut fp_actual_count = 0;
    for item in input.not_present.iter() {
        if bloom_filter.contains(&item) {
            fp_actual_count += 1
        }
    }

    let mut tn_actual_count = 0;
    for item in input.data.iter() {
        if !bloom_filter.contains(&item) {
            tn_actual_count += 1;
        }
    }

    let fp_actual_rate = fp_actual_count as f64 / (input.num_items) as f64;
    println!(
        "FP actual count: {}, TN actual count: {}, Data length: {}, FP actual rate: {}, Configured: {}",
        fp_actual_count,
        tn_actual_count,
        input.data.len(),
        fp_actual_rate,
        input.false_positive_rate
    );
    assert!(fp_actual_rate < input.false_positive_rate);
}

impl Arbitrary for BloomTestInput {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let num_items = rand::thread_rng().gen_range(0..2_000_000_000);
        let false_positive_rate = rand::thread_rng().gen_range(0.0001..0.9999);
        let mut data = Vec::<u32>::arbitrary(g);
        let not_present = Vec::<u32>::arbitrary(g);

        data.retain(|e| !not_present.contains(e));

        BloomTestInput {
            num_items,
            false_positive_rate,
            data,
            not_present: not_present.into_iter().collect(),
        }
    }
}
