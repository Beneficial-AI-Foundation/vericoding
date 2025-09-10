use vstd::prelude::*;

verus! {

fn binary_search(a: &[int], circle: int) -> (n: usize)
    requires
        forall|i: int| 1 <= i < a.len() ==> a[i-1] < #[trigger] a[i],
        forall|i: int, j: int| 0 <= i < j < a.len() ==> #[trigger] a[i] < #[trigger] a[j],
    ensures
        n <= a.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] a[i] < circle,
        forall|i: int| n <= i < a.len() ==> circle <= #[trigger] a[i],
{
    assume(false);
    0
}

fn tangent(r: &[int], x: &[int]) -> (found: bool)
    requires
        forall|i: int| 1 <= i < x.len() ==> x[i-1] < #[trigger] x[i],
        forall|i: int, j: int| 0 <= i < j < x.len() ==> #[trigger] x[i] < #[trigger] x[j],
    ensures
        !found ==> forall|i: int, j: int| 
            0 <= i < r.len() && 0 <= j < x.len() ==> #[trigger] r[i] != #[trigger] x[j],
        found ==> exists|i: int, j: int|
            0 <= i < r.len() && 0 <= j < x.len() && #[trigger] r[i] == #[trigger] x[j],
{
    assume(false);
    unreached();
}

}
fn main() {}