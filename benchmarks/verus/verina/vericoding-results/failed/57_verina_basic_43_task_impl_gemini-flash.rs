// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Keeping the helper function as it is, as the issue is in the main code. */
spec fn sum_of_fourth_power_of_odd_numbers_recursive(n: nat) -> (result: nat)
    decreases n
{
    if n == 0 {
        0
    } else {
        let prev_sum = sum_of_fourth_power_of_odd_numbers_recursive((n - 1) as nat);
        let term: nat = (2 * n - 1) as nat;
        prev_sum + term * term * term * term
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: nat) -> (result: nat)
    ensures
        15 * result == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed the term calculation to ensure all intermediate values are `nat` for executable code. */
{
    let mut i: nat = 1;
    let mut sum: nat = 0;

    while i <= n
        invariant
            0 <= i,
            i <= n + 1,
            sum == sum_of_fourth_power_of_odd_numbers_recursive(i - 1),
    {
        let two_i: nat = (2 * i) as nat;
        let term_intermediate: nat = two_i - 1;
        let term: nat = term_intermediate;
        sum = sum + term * term * term * term;
        i = i + 1;
    }

    sum
}
// </vc-code>

}
fn main() {}