use core::num;
use std::borrow::Borrow;
use std::cmp::max;
use std::hash::Hasher;
use std::{hash::Hash, marker::PhantomData};

use siphasher::sip::SipHasher24;

use crate::error::PDSAResult as Result;

use super::{calculate_alpha, create_hasher_with_key, generate_random_seed, validate};
const TWO_POW_32: f64 = (1_i64 << 32_i64) as f64;

pub struct HyperLogLog<T: Hash + Eq> {
    alpha: f64,
    precision: usize,
    num_buckets_m: usize,
    buckets: Vec<u8>,
    hasher: SipHasher24,
    _p: PhantomData<T>,
}

impl<T: Hash + Eq> HyperLogLog<T> {
    pub fn new(error_rate: f64) -> Result<Self> {
        validate(error_rate)?;
        let precision = (1.04 / error_rate).powi(2).log2().ceil() as usize; // log2(m)
        let num_buckets_m = 1 << precision; // 2^precision
        let alpha = calculate_alpha(num_buckets_m)?;

        //Instantiate our single hashing function
        let random_key = generate_random_seed();
        let hasher = create_hasher_with_key(random_key);

        let hll = HyperLogLog {
            alpha,
            precision,
            num_buckets_m,
            buckets: vec![0; num_buckets_m],
            hasher,
            _p: PhantomData,
        };

        Ok(hll)
    }

    pub fn insert<Q>(&mut self, item: &Q)
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let mut hasher = self.hasher;
        item.hash(&mut hasher);
        let hash = hasher.finish();

        let bucket_index = (hash >> (64 - self.precision)) as usize; // Take the first precision bits
        let estimate_bits_mask = (1 << (64 - self.precision)) - 1; // Create a mask for excluding the precision bits
        let estimate_bits = hash & estimate_bits_mask; // Rest of the bits
        let trailing_zeros = estimate_bits.leading_zeros() as u8 + 1; // Count the number of trailing zeros
        let prev_estimate = self.buckets[bucket_index]; // Get the previous estimate
        self.buckets[bucket_index] = max(prev_estimate, trailing_zeros) // Update the estimate if necessary
    }

    pub fn estimate(&self) -> usize {
        let m = self.num_buckets_m as f64;

        let mut sum = 0.0_f64;
        let mut empty_registers = 0;
        for &v in self.buckets.iter() {
            sum += 2.0_f64.powf(-(v as f64));
            if v == 0 {
                empty_registers += 1;
            }
        }

        let raw_estimate = self.alpha * m.powi(2) / sum;
        let estimate = self.correct_for_estimate_size(raw_estimate, m, empty_registers);

        estimate as usize
    }

    fn correct_for_estimate_size(&self, raw_estimate: f64, m: f64, empty_registers: usize) -> f64 {
        match raw_estimate {
            //Small range correction
            sr if raw_estimate <= 2.5_f64 * m => {
                if empty_registers > 0 {
                    m * (m / empty_registers as f64).ln()
                } else {
                    sr
                }
            }
            //Medium range correction
            mr if raw_estimate <= (TWO_POW_32 / 30.0_f64) => mr,
            //Large range correction
            lr => -TWO_POW_32 * (1.0 - lr / TWO_POW_32).ln(),
        }
    }

    pub fn alpha(&self) -> f64 {
        self.alpha
    }

    pub fn num_buckets_m(&self) -> usize {
        self.num_buckets_m
    }

    pub fn precision(&self) -> usize {
        self.precision
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    #[test]
    fn test_b() -> Result<()> {
        let error_rate = 0.01;
        let hll = HyperLogLog::<&str>::new(error_rate)?;
        assert_eq!(hll.precision, 14);
        Ok(())
    }

    #[test]
    fn test_insertion_with_duplicates() -> Result<()> {
        let error_rate = 0.01;
        let mut hll: HyperLogLog<&str> = HyperLogLog::new(error_rate)?;

        let data = [
            "foo", "foo", "foo", "bar", "baz", "bar", "qux", "quux", "corge", "grault", "garply",
            "waldo",
        ];

        data.iter().for_each(|item| hll.insert(item));
        let actual_count = data.iter().collect::<HashSet<_>>().iter().count();
        let estimated_count = hll.estimate();

        let error = ((actual_count as f64 - estimated_count as f64) / (actual_count as f64)).abs();

        let estimated_error = 1.04 / ((1 << hll.precision()) as f64).sqrt();

        println!("Actual count : {actual_count}. Estimated count is {estimated_count}");
        println!("Actual Error is : {error}. Estimated error is {estimated_error}");
        println!(
            "Number of buckets : {}. Precision : {}",
            hll.num_buckets_m(),
            hll.precision()
        );
        assert!(error >= 0.0);
        assert!(error <= estimated_error);

        Ok(())
    }
}
