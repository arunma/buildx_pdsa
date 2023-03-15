use std::borrow::Borrow;
use std::cmp::min;
use std::{hash::Hash, marker::PhantomData};

use siphasher::sip128::Hasher128;
use siphasher::sip128::SipHasher24;

use crate::error::PDSAError::*;
use crate::error::PDSAResult as Result;

use super::{create_hasher_with_key, generate_random_key, optimal_k, optimal_m};

#[derive(Debug)]
pub struct CountMinSketch<K: Hash + Eq> {
    expected_num_items: usize,
    false_positive_rate: f64,
    hasher: SipHasher24,
    counter: Vec<Vec<u8>>,
    m: usize,
    k: usize,
    len: usize,
    _p: PhantomData<K>,
}

impl<K: Hash + Eq> CountMinSketch<K> {
    pub fn new(expected_num_items: usize, false_positive_rate: f64) -> Result<Self> {
        Self::validate(expected_num_items, false_positive_rate)?;
        let m = optimal_m(expected_num_items, false_positive_rate);
        let k = optimal_k(expected_num_items, m);
        let random_key = generate_random_key();
        let hasher = create_hasher_with_key(random_key);
        let counter = vec![vec![0u8; m]; k];

        Ok(CountMinSketch {
            expected_num_items,
            false_positive_rate,
            hasher,
            counter,
            m,
            k,
            len: 0,
            _p: PhantomData,
        })
    }

    pub fn insert<Q>(&mut self, key: &Q)
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let set_bits = self.get_set_bits(key, self.hasher);
        set_bits
            .iter()
            .enumerate()
            .for_each(|(ki, &sb)| self.counter[ki][sb] = self.counter[ki][sb].saturating_add(1));
        self.len += 1
    }

    pub fn estimated_count<Q>(&self, key: &Q) -> u8
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let set_bits = self.get_set_bits(key, self.hasher);
        let mut estimated_count = u8::MAX;
        for (ki, &sb) in set_bits.iter().enumerate() {
            if self.counter[ki][sb] == 0 {
                return 0;
            } else {
                estimated_count = min(estimated_count, self.counter[ki][sb])
            }
        }
        estimated_count
    }

    /// Computes the set of bit indices to be set for an item
    fn get_set_bits<Q>(&self, item: &Q, hasher: SipHasher24) -> Vec<usize>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (hash1, hash2) = self.get_hash_pair(item, hasher);
        let mut set_bits = Vec::with_capacity(self.k);
        if self.k == 1 {
            let bit = hash1 % self.m as u64;
            set_bits.push(bit as usize);
            return set_bits;
        } else {
            for ki in 0..self.k as u64 {
                let hash = hash1.wrapping_add(ki.wrapping_mul(hash2));
                let bit = hash % self.m as u64;
                set_bits.push(bit as usize)
            }
        }

        set_bits
    }

    fn get_hash_pair<Q>(&self, item: &Q, mut hasher: SipHasher24) -> (u64, u64)
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        item.hash(&mut hasher);
        let hash128 = hasher.finish128().as_u128();
        let hash1 = (hash128 & 0xffff_ffff_ffff_ffff) as u64;
        let hash2 = (hash128 >> 64) as u64;
        (hash1, hash2)
    }

    /// Returns the number of hash functions used by the Min sketch.
    ///
    /// # Examples
    ///
    /// ```
    /// use buildx_pdsa::frequency::count_min_sketch::CountMinSketch;
    ///
    /// let sketch = CountMinSketch::<String>::new(1000, 0.01).unwrap();
    /// let k = sketch.number_of_hashes();
    /// assert_eq!(k, 7);
    /// ```

    pub fn number_of_hashes(&self) -> usize {
        self.k
    }

    /// Returns the number of bits used by the Min sketch.
    ///
    /// # Examples
    ///
    /// ```
    /// use buildx_pdsa::frequency::count_min_sketch::CountMinSketch;
    ///
    /// let sketch = CountMinSketch::<&str>::new(1000, 0.01).unwrap();
    /// let m = sketch.number_of_counters();
    /// assert_eq!(m, 9585);
    /// ```
    pub fn number_of_counters(&self) -> usize {
        self.m
    }

    /// Returns the number of items currently stored in the Min sketch.
    ///
    /// # Example
    ///
    /// ```
    /// use buildx_pdsa::frequency::count_min_sketch::CountMinSketch;
    ///
    /// let mut filter = CountMinSketch::new(1000, 0.01).unwrap();
    /// assert_eq!(filter.len(), 0);
    ///
    /// filter.insert("hello");
    /// assert_eq!(filter.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns if there are currently no items stored in the Count min sketch.
    ///
    /// # Example
    ///
    /// ```
    /// use buildx_pdsa::frequency::count_min_sketch::CountMinSketch;
    ///
    /// let mut filter = CountMinSketch::new(1000, 0.01).unwrap();
    /// assert_eq!(filter.is_empty(), true);
    ///
    /// filter.insert("hello");
    /// assert_eq!(filter.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the expected number of items to be inserted into the Min sketch.
    ///
    /// # Example
    ///
    /// ```
    /// use buildx_pdsa::frequency::count_min_sketch::CountMinSketch;
    ///
    /// let mut filter = CountMinSketch::<str>::new(1000, 0.01).unwrap();
    /// assert_eq!(filter.expected_num_items(), 1000);
    /// ```
    pub fn expected_num_items(&self) -> usize {
        self.expected_num_items
    }

    /// Returns the false positive rate of the Min sketch.
    ///
    /// # Example
    ///
    /// ```
    /// use buildx_pdsa::frequency::count_min_sketch::CountMinSketch;
    ///
    /// let mut filter = CountMinSketch::<str>::new(1000, 0.01).unwrap();
    /// assert_eq!(filter.false_positive_rate(), 0.01);
    /// ```
    pub fn false_positive_rate(&self) -> f64 {
        self.false_positive_rate
    }

    /// Validates the input parameters for a Min sketch.
    ///
    /// # Arguments
    ///
    /// * `num_items` - The expected number of items in the Min sketch.
    /// * `false_positive_rate` - The desired false positive rate for the Min sketch.
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
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::error::PDSAError::Input;
    use crate::error::PDSAResult as Result;
    use pretty_assertions::assert_eq;

    #[test]
    fn new_from_num_items_and_fp_rate() -> Result<()> {
        let bf: CountMinSketch<&str> = CountMinSketch::new(100, 0.01)?;
        assert_eq!(bf.number_of_hashes(), 7);

        let bf: CountMinSketch<&u64> = CountMinSketch::new(1000, 0.001)?;
        assert_eq!(bf.number_of_hashes(), 10);

        let bf: CountMinSketch<&String> = CountMinSketch::new(10000, 0.0001)?;
        assert_eq!(bf.number_of_hashes(), 13);

        Ok(())
    }

    #[test]
    fn invalid_num_items() {
        let result: Result<CountMinSketch<&str>> = CountMinSketch::new(0usize, 0.7f64);
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            Input("Number of items (num_items) must be greater than 0".into())
        );
    }

    #[test]
    fn invalid_fp_rate() {
        let result_fp1: Result<CountMinSketch<&str>> = CountMinSketch::new(1000usize, 0f64);
        assert_eq!(
            result_fp1.unwrap_err(),
            Input("False positive rate (false_positive_rate) must be between 0.0 and 1.0".into())
        );

        let result_fp2: Result<CountMinSketch<&str>> = CountMinSketch::new(1000usize, 1f64);
        assert_eq!(
            result_fp2.unwrap_err(),
            Input("False positive rate (false_positive_rate) must be between 0.0 and 1.0".into())
        );
    }

    #[test]
    fn insert_and_check() -> Result<()> {
        let mut bf: CountMinSketch<&str> = CountMinSketch::new(10, 0.01)?;
        bf.insert("hello");
        bf.insert("world");
        assert_eq!(bf.number_of_hashes(), 7);
        assert_eq!(bf.number_of_counters(), 95);
        assert_eq!(bf.estimated_count("world"), 1);
        assert_eq!(bf.estimated_count("hello"), 1);
        assert_eq!(bf.estimated_count("hel12lo1"), 0);

        Ok(())
    }
}
