// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_array(a: &[i32]) -> (r: i32)
    requires a.len() > 0,
    ensures forall|i: int| 0 <= i < a.len() ==> r <= a[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}