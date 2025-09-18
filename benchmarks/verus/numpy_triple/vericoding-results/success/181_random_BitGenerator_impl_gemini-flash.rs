// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct BitGeneratorState {

    pub seed: Option<u64>,

    pub internal_state: u64,
}
// </vc-preamble>

// <vc-helpers>

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
    let initial_state: u64;
    match seed {
        Some(s) => {
            if s == 0 {
                initial_state = 1; // numpy uses 1 if seed is 0
            } else {
                initial_state = s;
            }
        }
        None => {
            initial_state = 0; // indicates an unseeded generator
        }
    }
    BitGeneratorState { seed: seed, internal_state: initial_state }
}
// </vc-code>

}
fn main() {}