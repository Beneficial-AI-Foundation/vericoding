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

// <vc-helpers>
proof fn lemma_sum_base(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int)
    ensures sum(X_val, X_crd, v, b, b) == 0
{
    assert(sum(X_val, X_crd, v, b, b) == 0);
}

proof fn lemma_sum_unfold_b_lt_k(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int)
    requires
        b < k,
    ensures
        sum(X_val, X_crd, v, b, k) == sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b] as int],
    decreases k - b
{
    assert(sum(X_val, X_crd, v, b, k) == sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b] as int]);
}
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
    let mut y: Vec<int> = Vec::new();

    let mut i: usize = 0;
    while i + 1 < X_pos.len()
        invariant
            // preconditions preserved
            X_crd.len() >= 1,
            X_crd.len() == X_val.len(),
            X_pos.len() >= 1,
            forall|a: int, b: int| 0 <= a < b < X_pos.len() as int ==> #[trigger] X_pos[a] <= #[trigger] X_pos[b],
            forall|p: int| 0 <= p < X_crd.len() as int ==> #[trigger]
// </vc-code>

// 0 0 0 0 0 0 1 0
// 0 0 0 0 0 0 0 0
// 0 0 0 0 1 0 0 0
// 0 0 0 0 0 0 0 0
// 0 0 1 0 0 0 0 0
// 0 0 0 0 0 0 0 0
// 1 0 0 0 0 0 0 0
// 0 0 0 0 0 0 0 0

fn main() {
}

}