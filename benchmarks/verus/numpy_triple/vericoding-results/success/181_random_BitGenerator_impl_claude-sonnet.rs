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
    match seed {
        Some(s) => {
            let state = if s == 0 { 1 } else { s };
            BitGeneratorState {
                seed: seed,
                internal_state: state,
            }
        },
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