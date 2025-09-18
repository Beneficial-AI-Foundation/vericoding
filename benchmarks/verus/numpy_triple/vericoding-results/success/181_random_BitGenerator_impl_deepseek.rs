// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct BitGeneratorState {

    pub seed: Option<u64>,

    pub internal_state: u64,
}
// </vc-preamble>

// <vc-helpers>
fn numpy_random_bit_generator_helper(seed: Option<u64>) -> (internal_state: u64)
    ensures
        seed.is_Some() ==> internal_state != 0,
        seed.is_None() ==> internal_state == 0
{
    match seed {
        Some(s) => {
            let mut state = s;
            if state == 0 {
                state = 1;
            }
            state
        }
        None => 0,
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
    let internal_state = numpy_random_bit_generator_helper(seed);
    BitGeneratorState { seed, internal_state }
}
// </vc-code>

}
fn main() {}