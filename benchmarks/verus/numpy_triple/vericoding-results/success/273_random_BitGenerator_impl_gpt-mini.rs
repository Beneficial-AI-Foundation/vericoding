// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct BitGeneratorState {

    pub seed: Option<u64>,

    pub internal_state: u64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): compute initial_internal_state from optional seed with named return */
fn initial_internal_state(seed: Option<u64>) -> (result: u64)
    ensures
        seed.is_Some() ==> result != 0,
        seed.is_None() ==> result == 0,
{
    let res = match seed {
        Option::None => 0u64,
        Option::Some(s) => if s != 0 { s } else { 1u64 },
    };
    res
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
    /* code modified by LLM (iteration 3): construct BitGeneratorState using helper */
    let internal = initial_internal_state(seed);
    BitGeneratorState { seed: seed, internal_state: internal }
}
// </vc-code>

}
fn main() {}