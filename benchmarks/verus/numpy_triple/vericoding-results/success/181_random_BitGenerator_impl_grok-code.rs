// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct BitGeneratorState {

    pub seed: Option<u64>,

    pub internal_state: u64,
}
// </vc-preamble>

// <vc-helpers>
spec fn compute_internal_state(seed: Option<u64>) -> u64 {
    match seed {
        Some(s) => if s == 0 { 1 } else { s },
        None => 0
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
/* code modified by LLM (iteration 4): Implement internal_state computation directly in exec code */
{
    let internal_state = match seed {
        Some(s) => if s == 0 { 1 } else { s },
        None => 0
    };
    let result = BitGeneratorState { seed, internal_state };
    result
}
// </vc-code>

}
fn main() {}