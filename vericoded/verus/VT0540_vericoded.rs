// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct BitGeneratorState {

    pub seed: Option<u64>,

    pub internal_state: u64,
}
// </vc-preamble>

// <vc-helpers>
fn compute_internal_state(seed: Option<u64>) -> (s: u64)
    ensures
        seed.is_Some() ==> s != 0u64,
        seed.is_None() ==> s == 0u64,
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
    let s = compute_internal_state(seed);
    BitGeneratorState { seed, internal_state: s }
}
// </vc-code>

}
fn main() {}