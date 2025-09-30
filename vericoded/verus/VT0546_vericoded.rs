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
    match seed {
        None => {
            SFC64State { a: 0u64, b: 0u64, c: 0u64, counter: 0u64 }
        }
        Some(x) => {
            let a = if x == 0u64 { 1u64 } else { x };
            proof {
                if x == 0u64 {
                    assert(a == 1u64);
                    assert(a != 0u64);
                } else {
                    assert(a == x);
                    assert(x != 0u64);
                    assert(a != 0u64);
                }
            }
            SFC64State { a, b: 0u64, c: 0u64, counter: 0u64 }
        }
    }
}
// </vc-code>


}
fn main() {}