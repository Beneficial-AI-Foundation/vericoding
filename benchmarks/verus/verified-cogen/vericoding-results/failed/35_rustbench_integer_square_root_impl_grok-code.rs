// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    requires
        n >= 1,
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): adding parentheses around all loop invariant expressions to fix compilation syntax error */
    let mut low: int = 1;
    let mut high: int = n as int;
    while low <= high
        invariant(1 <= low <= high + 1);
        invariant(high <= n as int);
        invariant(forall |r: int| 1 <= r < low ==> r * r <= n as int);
        invariant(forall |r: int| r > high ==> r * r > n as int);
    {
        let mid: int = low + (high - low) / 2;
        if (mid * mid) <= (n as int) {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    (high as i32)
}
// </vc-code>

}
fn main() {}