// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct BitGeneratorState {

    pub seed: Option<u64>,

    pub internal_state: u64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [Replaced `is_Some` and `is_None` with pattern matching to avoid deprecated methods. This also fixes the mode spec error that was occurring when `is_Some` was called in a spec context.] */
fn calculate_initial_state(seed: Option<u64>) -> (result: u64)
    ensures
        seed.is_Some() ==> result != 0,
        seed.is_None() ==> result == 0,
{
    match seed {
        Option::Some(_) => 1,
        Option::None => 0,
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
/* code modified by LLM (iteration 2): [The code body was correct in the previous iteration, but was re-submitted for completeness.] */
{
    let initial_state = calculate_initial_state(seed);
    BitGeneratorState {
        seed: seed,
        internal_state: initial_state,
    }
}
// </vc-code>

}
fn main() {}