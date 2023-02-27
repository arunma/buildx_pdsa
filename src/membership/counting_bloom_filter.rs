use std::fmt::Debug;
use std::{hash::Hash, marker::PhantomData};

use siphasher::sip128::{Hasher128, SipHasher24};

use crate::error::PDSAResult as Result;
use crate::membership::{
    create_hasher_with_key, generate_random_key, optimal_k, optimal_m, validate,
};

#[derive(Debug)]
pub struct CountingBloomFilter<T: ?Sized + Hash> {
    //TODO
    counter: Vec<u8>,
    m: usize,
    k: usize,
    hasher: SipHasher24,
    _p: PhantomData<T>,
}

impl<T: ?Sized + Hash + Debug> CountingBloomFilter<T> {
    pub fn new(num_items: usize, false_positive_rate: f64) -> Result<Self> {
        validate(num_items, false_positive_rate)?;
        let m = optimal_m(num_items, false_positive_rate);
        let counter = vec![0; m];
        let k = optimal_k(num_items, m);
        let random_key = generate_random_key();
        let hasher = create_hasher_with_key(random_key);
        Ok(Self {
            counter,
            m,
            k,
            hasher,
            _p: PhantomData,
        })
    }

    pub fn insert(&mut self, item: &T) {
        self.get_set_bits(item, self.k, self.m, self.hasher)
            .iter()
            .for_each(|&i| self.counter[i] = self.counter[i].saturating_add(1));
    }

    pub fn delete(&mut self, item: &T) {
        let is_present = self.contains(item);
        if is_present {
            self.get_set_bits(item, self.k, self.m, self.hasher)
                .iter()
                .for_each(|&i| {
                    self.counter[i] = self.counter[i].saturating_sub(1);
                });
        }
    }

    pub fn contains(&self, item: &T) -> bool {
        self.get_set_bits(item, self.k, self.m, self.hasher)
            .iter()
            .all(|&i| self.counter[i] > 0)
    }

    pub fn estimated_count(&self, item: &T) -> u8 {
        self.get_set_bits(item, self.k, self.m, self.hasher)
            .iter()
            .fold(u8::MAX, |acc, &i| {
                if self.counter[i] < acc {
                    self.counter[i]
                } else {
                    acc
                }
            })
    }

    /// Returns the number of hash functions used by the Bloom filter.
    ///
    /// # Examples
    ///
    /// ```
    /// use pdsa::membership::counting_bloom_filter::CountingBloomFilter;
    ///
    /// let bloom_filter = CountingBloomFilter::<String>::new(1000, 0.01).unwrap();
    /// let k = bloom_filter.number_of_hashes();
    /// assert_eq!(k, 7);
    /// ```

    pub fn number_of_hashes(&self) -> usize {
        self.k
    }

    /// Returns the number of bits used by the Bloom filter.
    ///
    /// # Examples
    ///
    /// ```
    /// use pdsa::membership::counting_bloom_filter::CountingBloomFilter;
    ///
    /// let bloom_filter = CountingBloomFilter::<&str>::new(1000, 0.01).unwrap();
    /// let m = bloom_filter.number_of_counters();
    /// assert_eq!(m, 9585);
    /// ```
    pub fn number_of_counters(&self) -> usize {
        self.m
    }

    /// Computes the set of bit indices to be set for an item
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

    /// Computes the pair of 64-bit hashes for an item using the internal hasher
    fn get_hash_pair(&self, item: &T, mut hasher: SipHasher24) -> (u64, u64) {
        item.hash(&mut hasher);
        let hash128 = hasher.finish128().as_u128();
        let hash1 = (hash128 & 0xffff_ffff_ffff_ffff) as u64;
        let hash2 = (hash128 >> 64) as u64;
        (hash1, hash2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::PDSAError::Input;
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
            Input("Number of items (num_items) must be greater than 0".into())
        );
    }

    #[test]
    fn invalid_fp_rate() {
        let result_fp1: Result<CountingBloomFilter<&str>> =
            CountingBloomFilter::new(1000usize, 0f64);
        assert_eq!(
            result_fp1.unwrap_err(),
            Input("False positive rate (false_positive_rate) must be between 0.0 and 1.0".into())
        );

        let result_fp2: Result<CountingBloomFilter<&str>> =
            CountingBloomFilter::new(1000usize, 1f64);
        assert_eq!(
            result_fp2.unwrap_err(),
            Input("False positive rate (false_positive_rate) must be between 0.0 and 1.0".into())
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
