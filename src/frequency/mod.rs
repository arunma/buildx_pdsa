pub mod count_min_sketch;

use crate::error::PDSAError::InputError;
use crate::error::PDSAResult as Result;
use siphasher::sip128::SipHasher24;

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

/// Calculates the optimal size of the counter given the maximum "allowable" error.
///
/// The optimal number of buckets is calculated using the
/// following formula:
/// optimal_m = ceil(e / epsilon)
///
/// eg. If the epsilon is 0.01 (1%), then the estimate of the count for a given item is within 1% of the actual count.
///
/// # Arguments
///
/// * `epsilon` - The maximum "allowable" difference from the actual value.
///
/// # Returns
///
/// Returns the optimal bucket size
///
fn optimal_m(epsilon: f64) -> usize {
    (2.71828 / epsilon).ceil() as usize
}

/// Calculates the optimal number of hash functions for a false positive rate.
///
/// # Arguments
///
/// * `delta` - Maximum allowed probability of the value being incorrect by more than the `epsilon` value.
///
/// # Returns
///
/// Returns the optimal number of hash functions
///
fn optimal_k(delta: f64) -> usize {
    (1.0 / delta).ln().ceil() as usize
}

fn validate(epsilon: f64, delta: f64) -> Result<()> {
    if epsilon <= 0.0 || epsilon >= 1.0 {
        return Err(InputError(
            "False positive rate (false_positive_rate) must be between 0.0 and 1.0".into(),
        ));
    }
    if delta <= 0.0 || delta >= 1.0 {
        return Err(InputError(
            "False positive rate (false_positive_rate) must be between 0.0 and 1.0".into(),
        ));
    }
    Ok(())
}
