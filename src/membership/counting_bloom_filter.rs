use std::{hash::Hash, marker::PhantomData};

use siphasher::sip128::SipHasher24;

use crate::error::PDSAError::Input;
use crate::error::PDSAResult as Result;

use super::{create_hasher_with_key, generate_random_key, optimal_k, optimal_m, validate};

#[derive(Debug)]
pub struct CountingBloomFilter<T: ?Sized + Hash> {
    //TODO
    counter: Vec<u32>,
    m: usize,
    k: u32,
    hasher: SipHasher24,
    _p: PhantomData<T>,
}

impl<T: ?Sized + Hash> CountingBloomFilter<T> {
    pub fn new(num_items: usize, false_positive_rate: f64) -> Result<Self> {
        validate(num_items, false_positive_rate)?;
        let m = optimal_m(num_items, false_positive_rate);
        let k = optimal_k(num_items, m);
        let counter = vec![0; m];
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
        //TODO Increment counter for every item addition
    }

    pub fn delete(&mut self, item: &T) {
        //TODO
    }

    pub fn contains(&self, item: &T) -> bool {
        todo!()
    }

    pub fn count(&self, item: &T) -> u32 {
        //TODO
        0
    }
}
