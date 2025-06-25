use vstd::prelude::*;

verus! {

pub fn search_recursive(a: Seq<f64>, i: int, j: int, x: f64) -> (k: int)
    requires
        0 <= i <= j <= a.len(),
        forall|p: int, q: int| i <= p < q < j ==> a[p] >= a[q],
    ensures
        i <= k <= j,
        forall|r: int| i <= r < k ==> a[r] >= x,
        forall|r: int| k <= r < j ==> a[r] < x,
{
}

pub fn search_loop(a: Seq<f64>, i: int, j: int, x: f64) -> (k: int)
    requires
        0 <= i <= j <= a.len(),
        forall|p: int, q: int| i <= p < q < j ==> a[p] >= a[q],
    ensures
        i <= k <= j,
        forall|r: int| i <= r < k ==> a[r] >= x,
        forall|r: int| k <= r < j ==> a[r] < x,
{
}

pub fn test(a: Seq<f64>, x: f64)
    requires
        forall|p: int, q: int| 0 <= p < q < a.len() ==> a[p] >= a[q],
{
}

}