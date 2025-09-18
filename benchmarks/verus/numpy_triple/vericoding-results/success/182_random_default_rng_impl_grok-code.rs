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
/* helper modified by LLM (iteration 4): Changed spec fn to concrete fn to fix ghost assignment compilation error */
fn generate_nonzero_state(seed: Option<u64>) -> (result: u64)
    ensures
        seed.is_some() ==> result != 0
{
    match seed {
        Some(s) => if s == 0 { 1 } else { s },
        None => 1,
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
/* code modified by LLM (iteration 4): Call concrete helper to generate state ensuring non-zero when seed is Some */
{
    let state = generate_nonzero_state(seed);
    Generator {
        bit_generator: BitGenerator {
            state,
            seed,
        },
        initialized: true,
    }
}
// </vc-code>

}
fn main() {}