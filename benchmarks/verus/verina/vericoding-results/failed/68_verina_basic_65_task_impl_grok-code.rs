// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed forall quantifiers from loop invariants to resolve trigger inference issue */
    let mut low: usize = 0;
    let mut high: usize = n;
    while low < high
        invariant
            0 <= low <= high <= n,
        decreases high - low,
    {
        let mid: usize = (low + high + 1) / 2;
        if (mid as u64) * (mid as u64) <= (n as u64) {
            low = mid;
        } else {
            if mid > 0 {
                high = mid - 1;
            } else {
                high = 0;
            }
        }
    }
    low
}
// </vc-code>

}
fn main() {}