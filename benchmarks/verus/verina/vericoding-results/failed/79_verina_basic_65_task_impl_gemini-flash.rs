// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Addensures clause on mid-calculation to prevent overflow. Refines invariant to prevent issues on `current_high >= low - 1` and `current_low <= high + 1`*/
fn isqrt_iterative_helper(n: usize, low: usize, high: usize) -> (result: usize)
    requires
        high >= low,
    ensures
        result * result <= n,
        (result + 1) * (result + 1) > n,
{
    let mut final_result = low;
    let mut current_low = low;
    let mut current_high = high;

    while current_low <= current_high
        invariant
            current_high + 1 >= current_low,
            final_result * final_result <= n,
            final_result <= current_high,
            current_low <= high + 1,
            current_high >= low - 1,
        decreases current_high - current_low
    {
        let mid = current_low + (current_high - current_low) / 2;
        if mid * mid <= n {
            final_result = mid;
            current_low = mid + 1;
        } else {
            current_high = mid - 1;
        }
    }
    final_result
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `isqrt_iterative_helper` call parameters. Now, `n` is provided as the value for which to find the square root, and `0` and `n` define the initial search range. This is appropriate as the square root of `n` will be between `0` and `n` (inclusive). */
{
    isqrt_iterative_helper(n, 0, n)
}
// </vc-code>

}
fn main() {}