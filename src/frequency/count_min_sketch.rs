use std::borrow::Borrow;
use std::cmp::min;
use std::{hash::Hash, marker::PhantomData};

use siphasher::sip128::Hasher128;
use siphasher::sip128::SipHasher24;

use crate::error::PDSAError::*;
use crate::error::PDSAResult as Result;

use super::{create_hasher_with_key, generate_random_key, optimal_k, optimal_m, validate};

#[derive(Debug)]
pub struct CountMinSketch<K: Hash + Eq> {
    epsilon: f64,
    delta: f64,
    hasher: SipHasher24,
    counter: Vec<Vec<u32>>,
    m: usize,
    k: usize,
    len: usize,
    _p: PhantomData<K>,
}

impl<K: Hash + Eq> CountMinSketch<K> {
    pub fn new(max_variance_in_count: f64, fp_rate_of_count: f64) -> Result<Self> {
        validate(max_variance_in_count, fp_rate_of_count)?;
        let epsilon = max_variance_in_count;
        let delta = fp_rate_of_count;
        let m = optimal_m(delta);
        let k = optimal_k(fp_rate_of_count);
        let random_key = generate_random_key();
        let hasher = create_hasher_with_key(random_key);
        let counter = vec![vec![0_u32; m]; k];

        Ok(CountMinSketch {
            epsilon,
            delta,
            hasher,
            counter,
            m,
            k,
            len: 0,
            _p: PhantomData,
        })
    }

    pub fn insert(&mut self, key: &K) {
        let bucket_indices = self.get_bucket_indices(key, self.hasher);
        bucket_indices
            .iter()
            .enumerate()
            .for_each(|(ki, &bi)| self.counter[ki][bi] = self.counter[ki][bi].saturating_add(1));
        self.len += 1
    }

    pub fn estimated_count(&self, key: &K) -> u32 {
        let bucket_indices = self.get_bucket_indices(key, self.hasher);
        let mut estimated_count = u32::MAX;
        for (ki, &bi) in bucket_indices.iter().enumerate() {
            if self.counter[ki][bi] == 0 {
                return 0;
            } else {
                estimated_count = min(estimated_count, self.counter[ki][bi])
            }
        }
        estimated_count
    }

    /// Returns the bucket indices of k hash functions for an item
    fn get_bucket_indices(&self, item: &K, hasher: SipHasher24) -> Vec<usize> {
        let (hash1, hash2) = self.get_hash_pair(item, hasher);
        let mut bucket_indices = Vec::with_capacity(self.k);
        if self.k == 1 {
            let bit = hash1 % self.m as u64;
            bucket_indices.push(bit as usize);
            return bucket_indices;
        } else {
            for ki in 0..self.k as u64 {
                let hash = hash1.wrapping_add(ki.wrapping_mul(hash2));
                let bit = hash % self.m as u64;
                bucket_indices.push(bit as usize)
            }
        }

        bucket_indices
    }

    fn get_hash_pair(&self, item: &K, mut hasher: SipHasher24) -> (u64, u64) {
        item.hash(&mut hasher);
        let hash128 = hasher.finish128().as_u128();
        let hash1 = (hash128 & 0xffff_ffff_ffff_ffff) as u64;
        let hash2 = (hash128 >> 64) as u64;
        (hash1, hash2)
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

    pub fn max_variance_in_count(&self) -> f64 {
        self.epsilon
    }

    pub fn fp_rate_of_count(&self) -> f64 {
        self.delta
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::error::PDSAResult as Result;
    use pretty_assertions::assert_eq;

    #[test]
    fn new_from_num_items_and_fp_rate() -> Result<()> {
        let bf: CountMinSketch<&str> = CountMinSketch::new(0.01, 0.01)?;
        assert_eq!(bf.number_of_hashes(), 5);

        let bf: CountMinSketch<&u64> = CountMinSketch::new(0.02, 0.001)?;
        assert_eq!(bf.number_of_hashes(), 7);

        let bf: CountMinSketch<&String> = CountMinSketch::new(0.01, 0.0001)?;
        assert_eq!(bf.number_of_hashes(), 10);
        assert_eq!(bf.number_of_counters(), 27183);

        Ok(())
    }

    #[test]
    fn insert_and_check() -> Result<()> {
        let mut bf: CountMinSketch<&str> = CountMinSketch::new(0.01, 0.01)?;
        bf.insert(&"hello");
        bf.insert(&"world");
        assert_eq!(bf.number_of_hashes(), 5);
        assert_eq!(bf.number_of_counters(), 272);
        assert_eq!(bf.estimated_count(&"world"), 1);
        assert_eq!(bf.estimated_count(&"hello"), 1);
        assert_eq!(bf.estimated_count(&"hel12lo1"), 0);

        Ok(())
    }

    #[test]
    fn insert_and_check_several_items() -> Result<()> {
        let mut bf: CountMinSketch<&str> = CountMinSketch::new(0.2, 0.01)?;

        for _ in 0..1000000 {
            bf.insert(&"a1");
            bf.insert(&"a2");
            bf.insert(&"a3");
            bf.insert(&"a4");
            bf.insert(&"a5");
            bf.insert(&"a6");
            bf.insert(&"a7");
        }

        assert_eq!(bf.number_of_hashes(), 5);
        assert_eq!(bf.number_of_counters(), 272);
        assert_eq!(bf.estimated_count(&"a1"), 1000000);
        assert_eq!(bf.estimated_count(&"a2"), 1000000);
        assert_eq!(bf.estimated_count(&"b1"), 0);

        Ok(())
    }
}
