use std::{
    collections::{BinaryHeap, HashMap},
    hash::Hash,
};

use super::count_min_sketch::CountMinSketch;
use crate::error::PDSAResult as Result;

#[derive(Eq)]
struct Counter<T: Hash + Eq> {
    item: T,
    count: usize,
}

impl<T: Hash + Eq> Ord for Counter<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.count.cmp(&self.count)
    }
}

impl<T: Hash + Eq> PartialOrd for Counter<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Hash + Eq> PartialEq for Counter<T> {
    fn eq(&self, other: &Self) -> bool {
        self.count == other.count
    }
}

struct HeavyHitters<T: Hash + Eq> {
    min_sketch: CountMinSketch<T>,
    heap: BinaryHeap<Counter<T>>,
    len: usize,
    heap_count: HashMap<T, usize>,
}

impl<'a, T: Hash + Eq> HeavyHitters<T> {
    pub fn new(
        expected_num_items: usize,
        false_positive_rate: f64,
        threshold: usize,
    ) -> Result<Self> {
        let min_sketch = CountMinSketch::new(expected_num_items, false_positive_rate)?;
        let heap = BinaryHeap::new();
        let heap_count = HashMap::new();
        Ok(Self {
            min_sketch,
            heap,
            len: 0,
            heap_count,
        })
    }

    /*     pub fn insert(&mut self, item: T) {
        self.min_sketch.insert(&item);
        self.len += 1;

        self.update_heavy_hitters(&item);
    } */
    /* fn update_heavy_hitters(&mut self, item: &T) {
           let estimate = self.min_sketch.estimated_count(item);
           //Update hashmap with 1
           self.heap_count.entry(item).or_insert(0)+=1;

           self.heap_count.entry(item).or_insert(0)+=1;
           if heap.len() < threshold {
               self.heap.push(Counter{item, count: self.heap_count.get(item)});
           }
           else{
               heap.
           }
       }
    */
    //pub fn heap_count()
}
