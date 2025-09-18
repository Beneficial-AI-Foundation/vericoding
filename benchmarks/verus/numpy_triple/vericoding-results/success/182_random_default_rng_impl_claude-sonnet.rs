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
/* helper modified by LLM (iteration 2): changed from spec fn to regular fn to allow calling from exec mode */
fn get_initial_state(seed: Option<u64>) -> (result: u64)
    ensures
        seed.is_some() ==> result != 0
{
    match seed {
        Some(s) => if s == 0 { 1 } else { s },
        None => 12345u64,
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
    /* code modified by LLM (iteration 2): fixed compilation error by calling exec mode helper function */
    let initial_state = get_initial_state(seed);
    Generator {
        bit_generator: BitGenerator {
            state: initial_state,
            seed: seed,
        },
        initialized: true,
    }
}
// </vc-code>

}
fn main() {}