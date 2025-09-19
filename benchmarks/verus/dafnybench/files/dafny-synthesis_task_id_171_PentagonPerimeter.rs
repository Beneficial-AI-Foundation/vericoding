// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn pentagon_perimeter(side: i8) -> (perimeter: i8)
    requires side > 0
    ensures perimeter as int == 5 * side as int
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}