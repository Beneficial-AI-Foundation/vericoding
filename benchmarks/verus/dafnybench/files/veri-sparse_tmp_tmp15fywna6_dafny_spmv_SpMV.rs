// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int) -> int
    decreases k - b
{
    if k <= b {
        0
    } else {
        sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b] as int]
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn SpMV(X_val: &[int], X_crd: &[nat], X_pos: &[nat], v: &[int]) -> (y: Vec<int>)
    requires 
        X_crd.len() >= 1,
        X_crd.len() == X_val.len(),
        forall|i: int, j: int| 0 <= i < j < X_pos.len() ==> X_pos[i] <= X_pos[j],
        forall|i: int| 0 <= i < X_crd.len() ==> X_crd[i] < v.len(),
        forall|i: int| 0 <= i < X_pos.len() ==> X_pos[i] <= X_val.len(),
        X_pos.len() >= 1,
    ensures
        y.len() + 1 == X_pos.len(),
        forall|i: int| 0 <= i < y.len() ==> y[i] == sum(X_val@, X_crd@, v@, X_pos[i] as int, X_pos[i + 1] as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}