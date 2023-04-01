use std::collections::HashMap;

use buildx_pdsa::frequency::count_min_sketch::CountMinSketch;
use quickcheck::Arbitrary;
use rand::Rng;

#[derive(Clone, Debug)]
struct CountMinSketchInput {
    epsilon: f64,
    delta: f64,
    data: Vec<u32>,
}

#[quickcheck_macros::quickcheck]
fn quickcheck_counting_bloom_filter(input: CountMinSketchInput) {
    dbg!(&input);
    let mut count_sketch = CountMinSketch::<u32>::new(input.epsilon, input.delta).unwrap();

    input.data.iter().for_each(|item| count_sketch.insert(item));
    let mut freq_map = HashMap::<u32, u32>::new();
    input.data.iter().for_each(|&item| {
        let count = freq_map.entry(item).or_insert(0);
        *count += 1;
    });
    assert!(input
        .data
        .iter()
        .all(|item| count_sketch.estimated_count(item) > 0));
}

impl Arbitrary for CountMinSketchInput {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let epsilon = rand::thread_rng().gen_range(0.01..0.10);
        let delta = rand::thread_rng().gen_range(0.01..0.10);
        let mut data = Vec::<u32>::arbitrary(g);
        let not_present = Vec::<u32>::arbitrary(g);

        data.retain(|e| !not_present.contains(e));

        CountMinSketchInput {
            epsilon,
            delta,
            data,
        }
    }
}
