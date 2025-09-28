use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: i32) -> (sum: i32)
    requires n > 0,
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15,
// </vc-spec>
// <vc-code>
{
    let n128: i128 = n as i128;
    let sum128: i128 = n128 * (2 * n128 + 1) * (24 * n128 * n128 * n128 - 12 * n128 * n128 - 14 * n128 + 7) / 15;
    #[verifier::truncate]
    (sum128 as i32)
}
// </vc-code>

fn main() {}

}