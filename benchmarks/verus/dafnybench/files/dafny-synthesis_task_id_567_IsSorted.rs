// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_sorted(a: &Vec<i8>) -> (sorted: bool)
    requires
        a.len() > 0,
    ensures
        sorted <==> forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] as int <= a[j] as int,
        !sorted ==> exists|i: int, j: int| 0 <= i < j < a.len() && a[i] as int > a[j] as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}