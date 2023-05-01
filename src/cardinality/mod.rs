pub mod hyperloglog;

use crate::error::PDSAError::InputError;
use crate::error::PDSAResult as Result;
use siphasher::sip::SipHasher24;

/// Generates a random 64-bit key used for hashing
pub fn generate_random_seed() -> [u8; 16] {
    let mut seed = [0u8; 32];
    getrandom::getrandom(&mut seed).unwrap();
    seed[0..16].try_into().unwrap()
}

/// Creates a `SipHasher24` hasher with a given 64-bit key
pub fn create_hasher_with_key(key: [u8; 16]) -> SipHasher24 {
    SipHasher24::new_with_key(&key)
}

fn calculate_alpha(num_buckets_m: usize) -> Result<f64> {
    if !(num_buckets_m >= 16 && num_buckets_m <= 65536) {
        return Err(InputError(format!(
            "Invalid number of buckets calculated {num_buckets_m}"
        )));
    }
    let alpha = match num_buckets_m {
        16 => 0.673,
        32 => 0.697,
        64 => 0.709,
        _ => 0.7213 / (1.0 + 1.079 / num_buckets_m as f64),
    };

    Ok(alpha)
}

fn validate(error_rate: f64) -> Result<()> {
    if error_rate <= 0.0 || error_rate >= 1.0 {
        return Err(InputError(format!(
            "Error rate must be between 0.0 and 1.0. Provided: {error_rate}"
        )));
    }
    Ok(())
}
