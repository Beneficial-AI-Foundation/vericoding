// <vc-preamble>
use vstd::prelude::*;

verus! {

struct BitGenerator {

    state: u64,

    seed: Option<u64>,
}

struct Generator {

    bit_generator: BitGenerator,

    initialized: bool,
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn default_rng(seed: Option<u64>) -> (result: Generator)
    ensures
        result.initialized == true,
        result.bit_generator.seed == seed,
        seed.is_some() ==> result.bit_generator.state != 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): ensure non-zero state when seed is Some */
    let bit_gen = if seed.is_some() {
        let seed_val = seed.unwrap();
        BitGenerator {
            state: if seed_val == 0 { 1 } else { seed_val },
            seed: seed,
        }
    } else {
        BitGenerator {
            state: 1,
            seed: seed,
        }
    };
    Generator {
        bit_generator: bit_gen,
        initialized: true,
    }
}
// </vc-code>

}
fn main() {}