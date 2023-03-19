use std::fmt::Debug;
use std::{hash::Hash, marker::PhantomData};

use siphasher::sip128::{Hasher128, SipHasher24};

use crate::error::PDSAError::InputError;
use crate::error::PDSAResult as Result;

#[derive(Debug)]
pub struct CountingBloomFilter<T: ?Sized + Hash> {
    counter: Vec<u8>,
    m: usize,
    k: usize,
    hasher: SipHasher24,
    expected_num_items: usize,
    false_positive_rate: f64,
    len: usize,
    _p: PhantomData<T>,
}

impl<T: ?Sized + Hash + Debug> CountingBloomFilter<T> {
    pub fn new(expected_num_items: usize, false_positive_rate: f64) -> Result<Self> {
        validate(expected_num_items, false_positive_rate)?;
        let m = optimal_m(expected_num_items, false_positive_rate);
        let counter = vec![0; m];
        let k = optimal_k(expected_num_items, m);
        let random_key = generate_random_key();
        let hasher = create_hasher_with_key(random_key);
        Ok(Self {
            counter,
            m,
            k,
            hasher,
            expected_num_items,
            false_positive_rate,
            len: 0,
            _p: PhantomData,
        })
    }

    pub fn insert(&mut self, item: &T) {
        self.get_set_bits(item, self.k, self.m, self.hasher)
            .iter()
            .for_each(|&i| self.counter[i] = self.counter[i].saturating_add(1));
        self.len += 1;
    }

    pub fn delete(&mut self, item: &T) {
        let is_present = self.contains(item);
        if is_present {
            self.get_set_bits(item, self.k, self.m, self.hasher)
                .iter()
                .for_each(|&i| {
                    self.counter[i] = self.counter[i].saturating_sub(1);
                });
            self.len -= 1;
        }
    }

    pub fn contains(&self, item: &T) -> bool {
        self.get_set_bits(item, self.k, self.m, self.hasher)
            .iter()
            .all(|&i| self.counter[i] > 0)
    }

    pub fn estimated_count(&self, item: &T) -> u8 {
        let mut retu = u8::MAX;
        for each in self.get_set_bits(item, self.k, self.m, self.hasher) {
            if self.counter[each] == 0 {
                return 0;
            }
            if self.counter[each] < retu {
                retu = self.counter[each];
            }
        }
        retu
    }

    pub fn number_of_hashes(&self) -> usize {
        self.k
    }

    pub fn number_of_counters(&self) -> usize {
        self.m
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn expected_num_items(&self) -> usize {
        self.expected_num_items
    }

    pub fn false_positive_rate(&self) -> f64 {
        self.false_positive_rate
    }

    fn get_set_bits(&self, item: &T, k: usize, m: usize, hasher: SipHasher24) -> Vec<usize> {
        let (hash1, hash2) = self.get_hash_pair(item, hasher);
        let mut set_bits = Vec::with_capacity(k);
        if k == 1 {
            let bit = hash1 % m as u64;
            set_bits.push(bit as usize);
            return set_bits;
        }
        for ki in 0..k as u64 {
            let hash = hash1.wrapping_add(ki.wrapping_mul(hash2));
            let bit = hash % m as u64;
            set_bits.push(bit as usize);
        }
        assert!(set_bits.len() == k);
        set_bits
    }

    fn get_hash_pair(&self, item: &T, mut hasher: SipHasher24) -> (u64, u64) {
        item.hash(&mut hasher);
        let hash128 = hasher.finish128().as_u128();
        let hash1 = (hash128 & 0xffff_ffff_ffff_ffff) as u64;
        let hash2 = (hash128 >> 64) as u64;
        (hash1, hash2)
    }
}

fn validate(num_items: usize, false_positive_rate: f64) -> Result<()> {
    if num_items < 1 {
        return Err(InputError(
            "Number of items (num_items) must be greater than 0".into(),
        ));
    }
    if false_positive_rate <= 0.0 || false_positive_rate >= 1.0 {
        return Err(InputError(
            "False positive rate (false_positive_rate) must be between 0.0 and 1.0".into(),
        ));
    }
    Ok(())
}

fn generate_random_key() -> [u8; 16] {
    let mut seed = [0u8; 32];
    getrandom::getrandom(&mut seed).unwrap();
    seed[0..16].try_into().unwrap()
}

fn create_hasher_with_key(key: [u8; 16]) -> SipHasher24 {
    SipHasher24::new_with_key(&key)
}

fn optimal_m(num_items: usize, false_positive_rate: f64) -> usize {
    -(num_items as f64 * false_positive_rate.ln() / (2.0f64.ln().powi(2))).ceil() as usize
}

fn optimal_k(n: usize, m: usize) -> usize {
    let k = (m as f64 / n as f64 * 2.0f64.ln()).round() as usize;
    if k < 1 {
        1
    } else {
        k
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::PDSAError::InputError;
    use crate::error::PDSAResult as Result;
    use pretty_assertions::assert_eq;

    #[test]
    fn new_from_num_items_and_fp_rate() -> Result<()> {
        let bf: CountingBloomFilter<&str> = CountingBloomFilter::new(100, 0.01)?;
        assert_eq!(bf.number_of_hashes(), 7);

        let bf: CountingBloomFilter<&u64> = CountingBloomFilter::new(1000, 0.001)?;
        assert_eq!(bf.number_of_hashes(), 10);

        let bf: CountingBloomFilter<&String> = CountingBloomFilter::new(10000, 0.0001)?;
        assert_eq!(bf.number_of_hashes(), 13);

        Ok(())
    }

    #[test]
    fn invalid_num_items() {
        let result: Result<CountingBloomFilter<&str>> = CountingBloomFilter::new(0usize, 0.7f64);
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            InputError("Number of items (num_items) must be greater than 0".into())
        );
    }

    #[test]
    fn invalid_fp_rate() {
        let result_fp1: Result<CountingBloomFilter<&str>> =
            CountingBloomFilter::new(1000usize, 0f64);
        assert_eq!(
            result_fp1.unwrap_err(),
            InputError(
                "False positive rate (false_positive_rate) must be between 0.0 and 1.0".into()
            )
        );

        let result_fp2: Result<CountingBloomFilter<&str>> =
            CountingBloomFilter::new(1000usize, 1f64);
        assert_eq!(
            result_fp2.unwrap_err(),
            InputError(
                "False positive rate (false_positive_rate) must be between 0.0 and 1.0".into()
            )
        );
    }

    #[test]
    fn insert_and_check() -> Result<()> {
        let mut bf: CountingBloomFilter<str> = CountingBloomFilter::new(10, 0.01)?;
        bf.insert("hello");
        bf.insert("world");
        assert_eq!(bf.number_of_hashes(), 7);
        assert_eq!(bf.number_of_counters(), 95);
        assert_eq!(bf.contains("hello"), true);
        assert_eq!(bf.contains("world"), true);
        assert_eq!(bf.contains("hel12lo1"), false);
        assert_eq!(bf.estimated_count("world"), 1);
        assert_eq!(bf.estimated_count("hello"), 1);
        assert_eq!(bf.estimated_count("hel12lo1"), 0);

        Ok(())
    }

    #[test]
    fn delete_and_check() -> Result<()> {
        let mut bf: CountingBloomFilter<str> = CountingBloomFilter::new(10, 0.01)?;
        bf.insert("hello");
        bf.insert("world");
        assert_eq!(bf.estimated_count("world"), 1);
        assert_eq!(bf.estimated_count("hello"), 1);
        assert_eq!(bf.estimated_count("hel12lo1"), 0);

        bf.delete("world");
        bf.delete("hello12");
        assert_eq!(bf.estimated_count("world"), 0);
        assert_eq!(bf.estimated_count("hello"), 1);
        Ok(())
    }
}
