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
fn init_state(seed: Option<u64>) -> (state: u64)
    ensures
        seed.is_some() ==> state != 0
{
    match seed {
        Some(_) => 1u64,
        None => 0u64,
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
    let s = init_state(seed);
    let bit_generator = BitGenerator {
        state: s,
        seed,
    };
    let result = Generator {
        bit_generator,
        initialized: true,
    };
    result
}
// </vc-code>

}
fn main() {}