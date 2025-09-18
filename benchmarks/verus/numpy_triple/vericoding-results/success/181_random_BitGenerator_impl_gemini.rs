// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct BitGeneratorState {

    pub seed: Option<u64>,

    pub internal_state: u64,
}
// </vc-preamble>

// <vc-helpers>
fn initialize_state(seed: u64) -> (state: u64)
    ensures
        state != 0,
{
    if seed == 0 {
        1 // Use a default non-zero value if seed is 0
    } else {
        seed
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
    match seed {
        Some(s) => {
            let initial_state = initialize_state(s);
            BitGeneratorState {
                seed: seed,
                internal_state: initial_state,
            }
        }
        None => {
            BitGeneratorState {
                seed: seed,
                internal_state: 0,
            }
        }
    }
}
// </vc-code>

}
fn main() {}