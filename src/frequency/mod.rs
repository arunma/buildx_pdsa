use siphasher::sip128::SipHasher24;

pub mod count_min_sketch;
pub mod heavy_hitters;

/// Generates a random 128-bit key used for hashing
fn generate_random_key() -> [u8; 16] {
    let mut seed = [0u8; 32];
    getrandom::getrandom(&mut seed).unwrap();
    seed[0..16].try_into().unwrap()
}

/// Creates a `SipHasher24` hasher with a given 128-bit key
fn create_hasher_with_key(key: [u8; 16]) -> SipHasher24 {
    SipHasher24::new_with_key(&key)
}

/// Calculates the optimal size of the bit vector for a given number of items and false positive rate.
///
/// The optimal number of hash functions is calculated using the
/// following formula:
/// optimal_m = -(num_items * ln(false_positive_rate) / (2 * ln(2)^2))
///
/// This formula was derived by Solina and Kirsch.
///
/// # Arguments
///
/// * `num_items` - The number of items that will be stored in the Bloom filter.
/// * `false_positive_rate` - The desired false positive rate of the Bloom filter.
///
/// # Returns
///
/// Returns the optimal size of the bit vector for the given number of items and false positive rate.
///
fn optimal_m(num_items: usize, false_positive_rate: f64) -> usize {
    -(num_items as f64 * false_positive_rate.ln() / (2.0f64.ln().powi(2))).ceil() as usize
}

/// Calculates the optimal number of hash functions for a given number of items and size of the bit vector.
///
/// # Arguments
///
/// * `n` - The number of items that will be stored in the Bloom filter.
/// * `m` - The size of the bit vector used by the Bloom filter.
///
/// # Returns
///
/// Returns the optimal number of hash functions for the given number of items and size of the bit vector.
///
fn optimal_k(n: usize, m: usize) -> usize {
    let k = (m as f64 / n as f64 * 2.0f64.ln()).round() as usize;
    if k < 1 {
        1
    } else {
        k
    }
}
