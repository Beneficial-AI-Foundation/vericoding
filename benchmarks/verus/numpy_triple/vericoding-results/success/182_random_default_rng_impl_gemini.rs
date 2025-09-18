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
fn new_bit_generator(seed: Option<u64>) -> (bg: BitGenerator)
    ensures
        bg.seed == seed,
        seed.is_some() ==> bg.state != 0,
{
    let initial_state = match seed {
        Some(s) if s != 0 => s,
        _ => 1, // Default for seed=Some(0) or seed=None
    };

    BitGenerator {
        state: initial_state,
        seed: seed,
    }
}
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
    let bg = new_bit_generator(seed);
    Generator {
        bit_generator: bg,
        initialized: true,
    }
}
// </vc-code>

}
fn main() {}