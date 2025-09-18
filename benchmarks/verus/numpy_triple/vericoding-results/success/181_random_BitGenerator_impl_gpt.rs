// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct BitGeneratorState {

    pub seed: Option<u64>,

    pub internal_state: u64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced deprecated is_Some/is_None usage in exec code with pattern matching; preserves ensures about internal_state */
fn internal_state_from_seed(seed: Option<u64>) -> (r: u64)
    ensures
        seed.is_Some() ==> r != 0u64,
        seed.is_None() ==> r == 0u64
{
    match seed {
        Some(_) => 1u64,
        None => 0u64,
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_random_bit_generator(seed: Option<u64>) -> (result: BitGeneratorState)
    ensures 
        result.seed == seed,
        seed.is_Some() ==> result.internal_state != 0,
        seed.is_None() ==> result.internal_state == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): construct BitGeneratorState using helper with pattern matching to avoid deprecated spec calls in exec code */
    let internal = internal_state_from_seed(seed);
    BitGeneratorState { seed, internal_state: internal }
}
// </vc-code>

}
fn main() {}