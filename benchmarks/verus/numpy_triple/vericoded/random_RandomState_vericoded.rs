// <vc-preamble>
use vstd::prelude::*;

verus! {

/* A simple random state container that can generate random numbers
   This models the core functionality of numpy.random.RandomState.
   We focus on the random() method which generates random floats in [0, 1). */
struct RandomState {
    /* The seed value used to initialize the random number generator */
    seed: u8,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): normalize u8 to a small set of f32 values in [0, 1) without casts */
fn normalize_u8_to_unit_interval(seed: u8) -> f32 {
    let rem: u8 = seed % 8u8;
    match rem {
        0u8 => 0.0f32,
        1u8 => 0.125f32,
        2u8 => 0.25f32,
        3u8 => 0.375f32,
        4u8 => 0.5f32,
        5u8 => 0.625f32,
        6u8 => 0.75f32,
        _ => 0.875f32,
    }
}
// </vc-helpers>

// <vc-spec>
fn random(state: RandomState) -> (result: f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use helper without unsupported casts */
    let result = normalize_u8_to_unit_interval(state.seed);
    result
}
// </vc-code>


}
fn main() {}