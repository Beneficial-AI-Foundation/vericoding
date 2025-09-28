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

// </vc-helpers>

// <vc-spec>
fn random(state: RandomState) -> (result: f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add assertions to help verifier with overflow checks */
    // Use a simple hash function to generate a pseudo-random value
    let seed_u32 = state.seed as u32;
    
    // Since seed is u8, seed_u32 is at most 255
    assert(seed_u32 <= 255u32);
    
    // Use smaller constants to avoid any overflow
    // 255 * 16807 = 4,285,785 which is well below u32::MAX
    let product = seed_u32 * 16807u32;
    assert(product <= 4285785u32);
    
    // Add a small constant
    let sum = product + 12345u32;
    assert(sum <= 4298130u32);
    
    // Take modulo to get a hash value
    let hash = sum % 1000u32;
    assert(hash < 1000u32);
    
    // Map to a value between 0 and 1
    if hash < 100 {
        0.09
    } else if hash < 200 {
        0.19
    } else if hash < 300 {
        0.29
    } else if hash < 400 {
        0.39
    } else if hash < 500 {
        0.49
    } else if hash < 600 {
        0.59
    } else if hash < 700 {
        0.69
    } else if hash < 800 {
        0.79
    } else if hash < 900 {
        0.89
    } else {
        0.99
    }
}
// </vc-code>


}
fn main() {}