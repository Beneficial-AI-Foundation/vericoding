use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this simple calculation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn nth_nonagonal_number(n: int) -> (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
// </vc-spec>
// </vc-spec>

// <vc-code>
fn nth_nonagonal_number(n: int) -> (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    let result = n * (7 * n - 5) / 2;
    result
}
// </vc-code>

fn main() {}

}