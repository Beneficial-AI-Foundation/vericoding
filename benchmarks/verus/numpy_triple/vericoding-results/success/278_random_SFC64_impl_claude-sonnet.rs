// <vc-preamble>
use vstd::prelude::*;

verus! {

/* SFC64 state containing 256 bits split into four 64-bit words */
struct SFC64State {
    a: u64,
    b: u64,
    c: u64,
    counter: u64,
}
// </vc-preamble>

// <vc-helpers>
// Helper function to initialize SFC64 state from a seed
fn init_from_seed(seed: u64) -> (state: SFC64State)
    ensures
        state.a != 0 || state.b != 0 || state.c != 0 || state.counter != 0,
{
    // Use seed to initialize the state components
    // Ensure at least one component is non-zero
    let a = if seed == 0 { 1 } else { seed };
    let b = seed.wrapping_mul(0x9e3779b97f4a7c15);
    let c = seed.wrapping_mul(0xbf58476d1ce4e5b9);
    let counter = seed.wrapping_add(1);
    
    SFC64State { a, b, c, counter }
}
// </vc-helpers>

// <vc-spec>
fn sfc64(seed: Option<u64>) -> (state: SFC64State)
    ensures
        seed.is_none() ==> (state.a == 0 && state.b == 0 && state.c == 0 && state.counter == 0),
        seed.is_some() ==> (state.a != 0 || state.b != 0 || state.c != 0 || state.counter != 0),
// </vc-spec>
// <vc-code>
{
    match seed {
        None => {
            SFC64State { a: 0, b: 0, c: 0, counter: 0 }
        },
        Some(s) => {
            init_from_seed(s)
        }
    }
}
// </vc-code>


}
fn main() {}