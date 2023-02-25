//!
//! The BloomFilter struct is a probabilistic data structure that is used
//! to test whether an element is a member of a set.
//!
//! False positives are possible, but false negatives are not. In other words,
//! a query returns either "possibly in set" or "definitely not in set".
//! Elements can be added to the set, but not removed. The more elements
//! that are added to the set, the larger the probability of false positives.

//! This implementation uses the SipHash-2-4 128-bit hash function to generate hash
//! values for the filter, which is significantly faster than alternatives such as SHA-1.
//!
//! # Example
//!
//! ```
//! use pdsa::membership::bloom_filter::BloomFilter;
//!
//! let bloom_filter = BloomFilter::<u32>::new(100, 0.01).unwrap();
//! // Create a Bloom filter with 1000 items and a false positive rate of 1%
//! let mut bloom_filter = BloomFilter::new(1000, 0.01).unwrap();
//!
//! // Insert some items into the Bloom filter
//! bloom_filter.insert(&"foo");
//! bloom_filter.insert(&"bar");
//!
//! // Check if an item is in the Bloom filter
//! assert!(bloom_filter.contains(&"foo"));
//! assert!(!bloom_filter.contains(&"baz"));
//!
//! ```
//!

use std::{hash::Hash, marker::PhantomData};

use bit_vec::BitVec;
use siphasher::sip128::{Hasher128, SipHasher24};

use crate::error::PDSAError::Input;
use crate::error::PDSAResult as Result;

#[derive(Debug)]
pub struct BloomFilter<T: ?Sized + Hash> {
    bits: BitVec,
    m: usize,
    k: u32,
    hasher: SipHasher24,
    _p: PhantomData<T>,
}

impl<T: ?Sized + Hash> BloomFilter<T> {
    /// Creates a new Bloom filter with the optimal number of bits and hash functions based on the expected
    /// number of inserted items and the desired false positive rate.
    ///
    /// # Arguments
    ///
    /// * `num_items` - The number of items that will be inserted into the Bloom filter
    /// * `false_positive_rate` - The desired false positive rate
    ///
    /// # Errors
    ///
    /// An error is returned if `num_items` is zero or if `false_positive_rate` is greater than or equal to 1 or less than or equal to 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use pdsa::membership::bloom_filter::BloomFilter;
    ///
    /// let bloom_filter = BloomFilter::<u32>::new(100, 0.01).unwrap();
    /// ```

    pub fn new(num_items: usize, false_positive_rate: f64) -> Result<Self> {
        Self::validate(num_items, false_positive_rate)?;
        let m = Self::optimal_m(num_items, false_positive_rate);
        let k = Self::optimal_k(num_items, m);
        println!("m: {}, k: {}", m, k);
        let bits = BitVec::from_elem(m, false);
        let random_key = Self::generate_random_key();
        let hasher = Self::create_hasher_with_key(random_key);
        Ok(Self {
            bits,
            m,
            k,
            hasher,
            _p: PhantomData,
        })
    }
    /// Validates the input parameters for a Bloom filter.
    ///
    /// # Arguments
    ///
    /// * `num_items` - The expected number of items in the Bloom filter.
    /// * `false_positive_rate` - The desired false positive rate for the Bloom filter.
    ///
    /// # Errors
    ///
    /// Returns an `Input` error if any of the input parameters are invalid.
    ///
    fn validate(num_items: usize, false_positive_rate: f64) -> Result<()> {
        if num_items < 1 {
            return Err(Input(
                "Number of items (num_items) must be greater than 0".into(),
            ));
        }
        if false_positive_rate <= 0.0 || false_positive_rate >= 1.0 {
            return Err(Input(
                "False positive rate (false_positive_rate) must be between 0.0 and 1.0".into(),
            ));
        }
        Ok(())
    }

    /// Inserts an item into the Bloom filter.
    ///
    /// # Arguments
    ///
    /// * `item` - The item to insert into the Bloom filter.
    ///
    /// # Examples
    ///
    /// ```
    /// use pdsa::membership::bloom_filter::BloomFilter;
    ///
    /// let mut bloom_filter = BloomFilter::new(1000, 0.01).unwrap();
    /// let item = "Hello, world!";
    /// bloom_filter.insert(&item);
    /// assert!(bloom_filter.contains(&item));
    /// ```
    ///
    pub fn insert(&mut self, item: &T) {
        // Get the indices of the bits to set in the bit vector.
        self.get_set_bits(item)
            // For each index, set the corresponding bit in the bit vector to true.
            .iter()
            .for_each(|&bit| self.bits.set(bit, true))
    }

    /// Checks if an item is possibly in the Bloom filter.
    ///
    /// # Arguments
    ///
    /// * `item` - The item to check if it is possibly in the Bloom filter.
    ///
    /// # Returns
    ///
    /// Returns `true` if the item is possibly in the Bloom filter, and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use pdsa::membership::bloom_filter::BloomFilter;
    ///
    /// let mut bloom_filter = BloomFilter::new(1000, 0.01).unwrap();
    /// let item = "Hello, world!";
    /// bloom_filter.insert(&item);
    /// assert!(bloom_filter.contains(&item));
    /// ```
    pub fn contains(&self, item: &T) -> bool {
        // Get the indices of the bits to check in the bit vector.
        self.get_set_bits(item)
            // Check that all of the corresponding bits in the bit vector are true.
            .iter()
            .all(|&bit| self.bits.get(bit).unwrap())
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
    fn optimal_k(n: usize, m: usize) -> u32 {
        (m as f64 / n as f64 * 2.0f64.ln()).round() as u32
    }

    /// Converts the Bloom filter to a `Vec` of bytes.
    ///
    /// # Returns
    /// The compressed data in bytes

    pub fn to_bytes(&self) -> Vec<u8> {
        self.bits.to_bytes()
    }

    /// Returns the number of hash functions used by the Bloom filter.
    ///
    /// # Examples
    ///
    /// ```
    /// use pdsa::membership::bloom_filter::BloomFilter;
    ///
    /// let bloom_filter = BloomFilter::<String>::new(1000, 0.01).unwrap();
    /// let k = bloom_filter.number_of_hashes();
    /// assert_eq!(k, 7);
    /// ```

    pub fn number_of_hashes(&self) -> u32 {
        self.k
    }

    /// Returns the number of bits used by the Bloom filter.
    ///
    /// # Examples
    ///
    /// ```
    /// use pdsa::membership::bloom_filter::BloomFilter;
    ///
    /// let bloom_filter = BloomFilter::<&str>::new(1000, 0.01).unwrap();
    /// let m = bloom_filter.number_of_bits();
    /// assert_eq!(m, 9585);
    /// ```
    pub fn number_of_bits(&self) -> usize {
        self.m
    }

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

    /// Computes the set of bit indices to be set for an item
    fn get_set_bits(&self, item: &T) -> Vec<usize> {
        let (hash1, hash2) = self.get_hash_pair(item);
        let mut set_bits = Vec::with_capacity(self.k as usize);
        if self.k == 1 {
            let bit = hash1 % self.m as u64;
            set_bits.push(bit as usize);
            return set_bits;
        }
        for ki in 0..self.k as u64 {
            let hash = hash1.wrapping_add(ki.wrapping_mul(hash2));
            let bit = hash % self.m as u64;
            set_bits.push(bit as usize);
        }
        assert!(set_bits.len() == self.k as usize);
        set_bits
    }

    /// Computes the pair of 64-bit hashes for an item using the internal hasher
    fn get_hash_pair(&self, item: &T) -> (u64, u64) {
        let mut hasher = self.hasher;
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
        // Initial list verified with https://hur.st/bloomfilter/?n=10000&p=0.0001&m=&k=
        let bf: BloomFilter<&str> = BloomFilter::new(100, 0.01)?;
        assert_eq!(bf.to_bytes().len() * 8, 960);
        assert_eq!(bf.number_of_hashes(), 7);

        let bf: BloomFilter<&u64> = BloomFilter::new(1000, 0.001)?;
        assert_eq!(bf.to_bytes().len() * 8, 14384);
        assert_eq!(bf.number_of_hashes(), 10);

        let bf: BloomFilter<&String> = BloomFilter::new(10000, 0.0001)?;
        assert_eq!(bf.to_bytes().len() * 8, 191704);
        assert_eq!(bf.number_of_hashes(), 13);

        Ok(())
    }

    #[test]
    fn invalid_num_items() {
        let result: Result<BloomFilter<&str>> = BloomFilter::new(0usize, 0.7f64);
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            Input("Number of items (num_items) must be greater than 0".into())
        );
    }

    #[test]
    fn invalid_fp_rate() {
        let result_fp1: Result<BloomFilter<&str>> = BloomFilter::new(1000usize, 0f64);
        assert_eq!(
            result_fp1.unwrap_err(),
            Input("False positive rate (false_positive_rate) must be between 0.0 and 1.0".into())
        );

        let result_fp2: Result<BloomFilter<&str>> = BloomFilter::new(1000usize, 1f64);
        assert_eq!(
            result_fp2.unwrap_err(),
            Input("False positive rate (false_positive_rate) must be between 0.0 and 1.0".into())
        );
    }

    #[test]
    fn insert_and_check() -> Result<()> {
        let mut bf: BloomFilter<str> = BloomFilter::new(10, 0.01)?;
        bf.insert("hello");
        bf.insert("world");
        assert_eq!(bf.number_of_hashes(), 7);
        assert_eq!(bf.number_of_bits(), 95);
        println!("{:?}", bf.to_bytes());
        assert_eq!(bf.contains("hello"), true);
        assert_eq!(bf.contains("world"), true);
        assert_eq!(bf.contains("hel12lo1"), false);
        Ok(())
    }
}
