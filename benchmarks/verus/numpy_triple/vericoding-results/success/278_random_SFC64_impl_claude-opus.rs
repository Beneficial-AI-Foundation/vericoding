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

// </vc-helpers>

// <vc-spec>
fn sfc64(seed: Option<u64>) -> (state: SFC64State)
    ensures
        seed.is_none() ==> (state.a == 0 && state.b == 0 && state.c == 0 && state.counter == 0),
        seed.is_some() ==> (state.a != 0 || state.b != 0 || state.c != 0 || state.counter != 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix loop invariants to correctly track counter increments */
    match seed {
        None => {
            SFC64State { a: 0, b: 0, c: 0, counter: 0 }
        },
        Some(s) => {
            // Initialize state ensuring at least one component is non-zero
            let initial_a = if s == 0 { 0x9e3779b97f4a7c15u64 } else { s };
            let initial_b = if s == 0 { 0x9e3779b97f4a7c15u64 } else { s };
            let initial_c = if s == 0 { 0x9e3779b97f4a7c15u64 } else { s };
            let initial_counter = 1u64;
            
            let mut state = SFC64State { 
                a: initial_a, 
                b: initial_b, 
                c: initial_c, 
                counter: initial_counter 
            };
            
            // Perform mixing steps
            let mut i: u64 = 0;
            while i < 12
                invariant
                    i <= 12,
                    state.counter == initial_counter.wrapping_add(i),
                    initial_counter == 1,
                decreases 12 - i
            {
                let tmp = state.a.wrapping_add(state.b).wrapping_add(state.counter);
                state.a = state.b ^ (state.b >> 9);
                state.b = state.c.wrapping_add(state.c << 3);
                state.c = ((state.c << 24) | (state.c >> 40)).wrapping_add(tmp);
                state.counter = state.counter.wrapping_add(1);
                i = i + 1;
            }
            
            assert(state.counter >= 1);
            assert(state.a != 0 || state.b != 0 || state.c != 0 || state.counter != 0);
            
            state
        }
    }
}
// </vc-code>


}
fn main() {}