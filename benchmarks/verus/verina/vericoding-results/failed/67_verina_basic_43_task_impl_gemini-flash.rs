// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Changed type to `fn` */
fn sum_of_fourth_power_of_odd_numbers_recursive(n: nat) -> nat {
    if n == 0 {
        0
    } else {
        let prev_sum = sum_of_fourth_power_of_odd_numbers_recursive((n - 1) as nat);
        let term = (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1);
        prev_sum + term as nat
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: nat) -> (result: nat)
    ensures
        15 * result == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implemented the function body. */
{
    sum_of_fourth_power_of_odd_numbers_recursive(n)
}
// </vc-code>

}
fn main() {}