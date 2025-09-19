// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum_of_squares_of_first_n_odd_numbers(n: u8) -> (result: u8)
    requires n >= 0,
    ensures
        result as nat == (n as nat * (2 * n as nat - 1) * (2 * n as nat + 1)) / 3,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}