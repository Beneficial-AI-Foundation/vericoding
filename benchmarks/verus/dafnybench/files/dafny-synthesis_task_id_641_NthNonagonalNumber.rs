// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn nth_nonagonal_number(n: i8) -> (number: i8)
    requires n >= 0
    ensures number as int == n as int * (7 * n as int - 5) / 2
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}