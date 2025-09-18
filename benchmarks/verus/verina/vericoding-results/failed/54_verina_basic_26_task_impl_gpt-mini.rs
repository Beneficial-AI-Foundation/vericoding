// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial helper proving simple arithmetic */
proof fn trivial_helper() {
    proof {
        assert(1 + 1 == 2);
    }
}
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): return parity check directly without typed intermediate literals */
    n % 2 == 0
}
// </vc-code>

}
fn main() {}