use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nth_nonagonal_number(n: int) -> (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
// </vc-spec>
// <vc-code>
{
    n * (7 * n - 5) / 2
}
// </vc-code>

fn main() {}

}