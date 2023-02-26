# BuildX PDSA: A build_x project on Probabilistic Data Structures in Rust

BuildX PDSA is a collection of probabilistic data structures implemented in Rust. These data structures are useful for various applications where approximate answers or approximations to subsets are sufficient.

[![Crates.io](https://img.shields.io/crates/v/buildx_pdsa.svg)](https://crates.io/crates/buildx_pdsa)
[![Docs.rs](https://docs.rs/buildx_pdsa/badge.svg)](https://docs.rs/buildx_pdsa)
[![Build](https://github.com/arunma/buildx_pdsa/actions/workflows/rust.yml/badge.svg)](https://github.com/arunma/buildx_pdsa/actions/workflows/rust.yml)
[![License:MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Coverage Status](https://coveralls.io/repos/github/arunma/buildx_pdsa/badge.svg?branch=main)](https://coveralls.io/github/arunma/buildx_pdsa?branch=main)



## Installation

Add the following line to your Cargo.toml file:

```toml
[dependencies]
buildx_pdsa = "0.1.0"
```
## Usage 

### BloomFilter

```rust

use pdsa::BloomFilter;

fn main() {
    // Create a Bloom filter with 1000 items and a false positive rate of 1%
    let mut bloom_filter = BloomFilter::new(1000, 0.01).unwrap();

    // Insert some items into the Bloom filter
    bloom_filter.insert(&"foo");
    bloom_filter.insert(&"bar");

    // Check if an item is in the Bloom filter
    assert!(bloom_filter.contains(&"foo"));
    assert!(!bloom_filter.contains(&"baz"));
}
```

## Contribution
Contributions are welcome! If you find a bug or have a feature request, please open an issue on the GitHub repository. If you would like to contribute code, please fork the repository and submit a pull request.

See [CONTRIBUTING.md](CONTRIBUTING.md).


## License

BuildX PDSA is licensed under the MIT license. See the LICENSE file for details.



