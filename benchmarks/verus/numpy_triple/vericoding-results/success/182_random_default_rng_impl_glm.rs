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
fn generate_state(seed: Option<u64>) -> (result: u64)
    ensures
        seed.is_some() ==> result != 0,
{
    match seed {
        Some(s) => if s == 0 { 1 } else { s },
        None => 0,
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
    let bit_gen = BitGenerator {
        state: generate_state(seed),
        seed: seed,
    };
    Generator {
        bit_generator: bit_gen,
        initialized: true,
    }
}
// </vc-code>

}
fn main() {}