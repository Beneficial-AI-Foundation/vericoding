// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_sorted(a: &[i32]) -> (sorted: bool)
    requires
        a.len() > 0,
    ensures
        sorted <==> forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        !sorted ==> exists|i: int, j: int| 0 <= i < j < a.len() && a[i] > a[j],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}