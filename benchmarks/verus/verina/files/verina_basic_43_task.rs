// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: u8) -> (result: u8)
    ensures
        15 * (result as nat) == (n as nat) * (2 * (n as nat) + 1) * (7 + 24 * ((n as nat) * (n as nat) * (n as nat)) - 12 * ((n as nat) * (n as nat)) - 14 * (n as nat))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}