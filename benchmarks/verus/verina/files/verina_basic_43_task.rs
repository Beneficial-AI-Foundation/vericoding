// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn sum_of_fourth_power_of_odd_numbers(n: nat) -> nat
// </vc-spec>
// <vc-code>
{
    // impl-start
    0
    // impl-end
}

proof fn sum_of_fourth_power_of_odd_numbers_spec(n: nat)
    ensures
        15 * sum_of_fourth_power_of_odd_numbers(n) == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n),
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-code>


}
fn main() {}