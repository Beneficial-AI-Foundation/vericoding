// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed the square_pred helper since its logic can be directly integrated into the loop invariant to avoid trigger issues. */
// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added trigger annotations to quantified invariants to resolve trigger inference errors. The invariants ensure that `ans` satisfies the square root properties throughout the loop. */
{
    let mut low: usize = 0;
    let mut high: usize = n + 1;
    let mut ans: usize = 0;

    while low < high
        invariant
            0 <= low,
            low <= high,
            high <= n + 1,
            ans * ans <= n,
            // Property for `high`
            forall|k: usize| #[trigger] (high <= k) && k <= n ==> k * k > n,
            // Property for `low`
            forall|k: usize| 0 <= k && #[trigger] (k < low) ==> k * k <= n,
            // The actual square root (or `ans`) is between `low` and `high`
            // This means we are sure that the `ans` value is a valid candidate
            ans * ans <= n && (ans + 1) * (ans + 1) > n
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        // Proof that mid is within bounds and doesn't cause overflow
        proof {
            if high > low {
                assert((high - low) / 2 <= high - 1);
                assert(low + (high - low) / 2 <= low + high - 1);
                assert(low + (high - low) / 2 < high);
            }
        }

        if mid * mid <= n {
            ans = mid;
            proof { // Proof to show ans*ans <= n is preserved
                assert(ans * ans == mid * mid);
            }
            low = mid + 1;
            proof { // Proof for the new `ans` value in relation to `low`
                assert(ans * ans <= n);
                assert(mid * mid <= n);
                assert(low == mid + 1);
            }
        } else {
            high = mid;
            proof { // Proof for `high` invariant preservation
                assert(high == mid);
                assert(mid * mid > n);
            }
        }
    }
    ans
}
// </vc-code>

}
fn main() {}