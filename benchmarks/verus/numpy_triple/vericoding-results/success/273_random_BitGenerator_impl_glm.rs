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
    /* code modified by LLM (iteration 3): Removed custom OptionExt trait and rely on built-in Option functions */
    let internal_state = match seed {
        Some(s) => if s == 0 { 1 } else { s },
        None => 0,
    };
    BitGeneratorState { seed, internal_state }
}
// </vc-code>

}
fn main() {}