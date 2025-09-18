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

fn initialize_state(seed: u64) -> (state: u64)
    ensures state != 0
{
    if seed == 0 {
        1
    } else {
        seed
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
    let state = match seed {
        Some(s) => initialize_state(s),
        None => 1,
    };
    Generator {
        bit_generator: BitGenerator {
            state: state,
            seed: seed,
        },
        initialized: true,
    }
}
// </vc-code>

}
fn main() {}