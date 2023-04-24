use std::borrow::Borrow;
use std::cmp::max;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hasher;
use std::{hash::Hash, marker::PhantomData};

use siphasher::sip::SipHasher24;

use crate::error::PDSAError::InputError;
use crate::error::PDSAResult as Result;

use super::{create_hasher_with_key, generate_random_key};
const TWO_POW_32: f64 = (1_i64 << 32_i64) as f64;

pub struct HyperLogLog<T: Hash + Eq> {
    bias_correction_alpha: f64,
    precision: usize,
    buckets: usize,
    counters: Vec<u8>,
    hasher: SipHasher24,
    _p: PhantomData<T>,
}

impl<T: Hash + Eq> HyperLogLog<T> {
    pub fn new(error_rate: f64) -> Result<Self> {
        Self::validate(error_rate)?;
        let precision = (1.04 / error_rate).powi(2).ln().ceil() as usize;
        let buckets = 1 << precision;
        let bias_correction_alpha = Self::alpha(buckets);
        let random_key = generate_random_key();
        let hasher = create_hasher_with_key(random_key);

        let hll = HyperLogLog {
            bias_correction_alpha,
            precision,
            buckets,
            counters: vec![0; buckets],
            hasher,
            _p: PhantomData,
        };

        Ok(hll)
    }

    fn alpha(buckets: usize) -> f64 {
        match buckets {
            16 => 0.673,
            32 => 0.697,
            64 => 0.709,
            b => 0.723 / (1.0 + 1.079 / b as f64),
        }
    }

    fn validate(error_rate: f64) -> Result<()> {
        if error_rate <= 0.0 || error_rate >= 1.0 {
            return Err(InputError("Error rate must be between 0.0 and 1.0".into()));
        }
        Ok(())
    }

    pub fn insert<Q>(&mut self, item: &Q)
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let mut hasher = self.hasher;
        item.hash(&mut hasher);
        let hash = hasher.finish();
        println!("Binary hash : {hash:b}");
        println!("Precision: {}", self.precision);
        let bucket_index = (hash >> (64 - self.precision)) as usize; //first bits
        println!("bucket index : {bucket_index:b}");
        println!("bucket index value : {bucket_index}");
        let rest_bits_mask = 2u64.pow(64 - self.precision as u32) - 1;
        println!("rest bits mask : {rest_bits_mask:b}");
        let rest_bits = hash & rest_bits_mask; //rest of the bits
        println!("rest bits : {rest_bits:b}");
        let estimate: u8 = 1 + rest_bits.trailing_zeros() as u8;
        println!("estimate : {estimate}");
        let prev_estimate = self.counters[bucket_index];
        println!("previous estimate : {prev_estimate}");
        self.counters[bucket_index] = max(prev_estimate, estimate);
    }

    pub fn estimate(&self) -> usize {
        let mut sum = 0f64;
        for c in self.counters.iter() {
            sum += (0.5_f64).powi(*c as i32);
        }
        let harmonic_mean = self.buckets as f64 / sum;

        let raw_estimate = self.bias_correction_alpha * self.buckets as f64 * harmonic_mean;

        let estimate = match raw_estimate {
            //Small range correction
            sr if raw_estimate <= 2.5_f64 * self.buckets as f64 => {
                let v = self.empty_registers() as f64;
                if v == 0f64 {
                    sr
                } else {
                    self.buckets as f64 * (self.buckets as f64 / v).ln()
                }
            }
            //Medium range correction
            mr if raw_estimate <= (TWO_POW_32 / 30f64) => mr,
            //Large range correction
            lr => -TWO_POW_32 * (1.0 - lr / TWO_POW_32).ln(),
        };

        estimate as usize
    }

    pub fn empty_registers(&self) -> usize {
        self.counters.iter().filter(|&e| *e == 0).count()
    }
}

#[cfg(test)]
mod test_super {
    use super::*;

    #[test]
    fn test_insertion() -> Result<()> {
        let mut hll: HyperLogLog<&str> = HyperLogLog::new(0.1)?;
        hll.insert("hello");
        hll.insert("hello1");
        hll.insert("hello2");
        hll.insert("hello3");
        hll.insert("hello4");
        let estimate = hll.estimate();
        println!("Estimate : {estimate}");
        Ok(())
    }
}
