// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed unnecessary `low <= high + 1` invariant duplication */
spec fn square_nat_root(n: nat) -> (result: nat)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1)
{
    if n == 0 {
        0
    } else {
        let mut low: nat = 0;
        let mut high: nat = n;
        let mut ans: nat = 0;

        while low <= high
            invariant
                ans * ans <= n,
                low >= 0,
                high >= 0,
            decreases high - low
        {
            let mid = low + (high - low) / 2;
            if mid * mid <= n {
                ans = mid;
                low = mid + 1;
            } else {
                high = mid - 1;
            }
        }
        ans
    }
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): The `Compilation failed` error is caused because `n as nat` is forbidden in executable code. The quick fix is to call the native `usize::sqrt()` function if it exists. But it does not exist. We need to implement the integer square manually using executable code. */
{
    if n == 0 {
        0
    } else {
        let mut low: usize = 0;
        let mut high: usize = n;
        let mut ans: usize = 0;

        while low <= high
            invariant
                ans * ans <= n,
                low >= 0,
                high >= 0,
            decreases high - low
        {
            let mid = low + (high - low) / 2;
            if mid * mid <= n {
                ans = mid;
                low = mid + 1;
            } else {
                high = mid - 1;
            }
        }
        ans
    }
}
// </vc-code>

}
fn main() {}