pub mod hyperloglog;

use siphasher::sip::SipHasher24;

/// Generates a random 64-bit key used for hashing
pub fn generate_random_key() -> [u8; 16] {
    let mut seed = [0u8; 32];
    getrandom::getrandom(&mut seed).unwrap();
    seed[0..16].try_into().unwrap()
}

/// Creates a `SipHasher24` hasher with a given 64-bit key
pub fn create_hasher_with_key(key: [u8; 16]) -> SipHasher24 {
    SipHasher24::new_with_key(&key)
}
