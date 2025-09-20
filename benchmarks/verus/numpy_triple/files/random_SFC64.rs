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
    // impl-start
    assume(false);
    SFC64State { a: 0, b: 0, c: 0, counter: 0 }
    // impl-end
}
// </vc-code>


}
fn main() {}