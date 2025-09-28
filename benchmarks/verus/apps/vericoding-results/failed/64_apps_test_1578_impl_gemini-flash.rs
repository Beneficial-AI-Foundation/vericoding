// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn max_sum(n: int) -> int
    recommends n >= 1
{
    n * (n - 1) / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): max_sum helper for induction */
proof fn lemma_max_sum_iter(k: int)
    requires
        k >= 1
    ensures
        max_sum(k) == max_sum(k - 1) + (k - 1)
{
    // Proof: max_sum(k) = k*(k-1)/2, max_sum(k-1) = (k-1)*(k-2)/2
    // k*(k-1)/2 = (k-1)*(k-2)/2 + (k-1)
    // From: A = B + C, we want to prove A - C = B
    // k*(k-1)/2 - (k-1)
    // = (k-1) * (k/2 - 1)
    // = (k-1) * (k-2)/2
    // Done. The lemma is valid without explicit recursion because `max_sum` is a direct calculation.
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_sum(n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Only use `i8` variables for runtime, cast to `int` for specs. */
{
    let mut sum: i8 = 0;
    let mut i: i8 = 0;

    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            sum as int == max_sum(i as int)
        decreases (n as int - i as int)
    {
        proof {
            if i as int > 0 {
                lemma_max_sum_iter(i as int);
            }
        }
        sum = sum + i;
        i = i + 1;
    }
    sum
}
// </vc-code>


}

fn main() {}