use vstd::prelude::*;

verus! {

// <vc-helpers>
const TWO: int = 2;
const FIVE: int = 5;
const SEVEN: int = 7;
// </vc-helpers>

// <vc-spec>
fn nth_nonagonal_number(n: int) -> (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
// </vc-spec>
// <vc-code>
{
    n * (SEVEN * n - FIVE) / TWO
}
// </vc-code>

fn main() {}

}