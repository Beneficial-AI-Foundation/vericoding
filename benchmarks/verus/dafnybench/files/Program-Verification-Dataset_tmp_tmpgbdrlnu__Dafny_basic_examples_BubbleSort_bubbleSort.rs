// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(a: Seq<i32>, from: int, to: int) -> bool
    recommends 0 <= from <= to <= a.len()
{
    forall|u: int, v: int| from <= u < v < to ==> a[u] <= a[v]
}

spec fn pivot(a: Seq<i32>, to: int, pvt: int) -> bool
    recommends 0 <= pvt < to <= a.len()
{
    forall|u: int, v: int| 0 <= u < pvt < v < to ==> a[u] <= a[v]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn bubbleSort(a: &mut Vec<i32>)
    requires 
        old(a).len() > 0,
    ensures 
        sorted(a@, 0, a.len() as int),
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}