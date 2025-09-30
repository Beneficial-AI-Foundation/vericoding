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
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            0 <= i < a.len(),
            forall|x: int, y: int| 0 <= x < y <= i ==> a[x] <= a[y],
        decreases a.len() - 1 - i
    {
        if a[i] > a[i+1] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}