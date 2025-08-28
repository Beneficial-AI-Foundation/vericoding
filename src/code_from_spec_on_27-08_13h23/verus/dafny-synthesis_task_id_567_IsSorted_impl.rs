use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_sorted_implies_order(a: &[i32], i: int, j: int)
    requires
        forall|k: int, l: int| 0 <= k < l < a.len() ==> a[k] <= a[l],
        0 <= i < j < a.len(),
    ensures
        a[i] <= a[j],
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_sorted(a: &[i32]) -> (sorted: bool)
    requires
        a.len() > 0,
    ensures
        sorted <==> forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        !sorted ==> exists|i: int, j: int| 0 <= i < j < a.len() && a[i] > a[j],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_sorted(a: &[i32]) -> (sorted: bool)
    requires
        a.len() > 0,
    ensures
        sorted <==> forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        !sorted ==> exists|i: int, j: int| 0 <= i < j < a.len() && a[i] > a[j],
{
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            0 <= i < a.len(),
            forall|k: int| 0 <= k < i as int ==> (k < (a.len() as int) - 1 ==> a[k] <= a[k + 1]),
    {
        if a[i] > a[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {
}

}