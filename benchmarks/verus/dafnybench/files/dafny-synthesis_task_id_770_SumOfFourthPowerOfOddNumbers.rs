// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: i8) -> (sum: i8)
    requires n > 0,
    ensures sum as int == n as int * (2 * n as int + 1) * (24 * n as int * n as int * n as int - 12 * n as int * n as int - 14 * n as int + 7) / 15,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}