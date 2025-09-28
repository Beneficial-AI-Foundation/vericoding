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
/* helper modified by LLM (iteration 5): No changes required, retaining correct helper. */
proof fn sum_append_lemma(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int)
    requires
        b <= k,
        k < X_val.len(),
        k < X_crd.len(),
        forall|i: int| b <= i <= k ==> X_crd[i] < v.len(),
    ensures
        sum(X_val, X_crd, v, b, k + 1) == sum(X_val, X_crd, v, b, k) + X_val[k] * v[X_crd[k] as int],
    decreases k - b
{
    if b < k {
        sum_append_lemma(X_val, X_crd, v, b + 1, k);
    }
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
/* code modified by LLM (iteration 5): fixed compilation errors by using usize for loop variables/indices and correcting types in invariants. */
{
    let mut y: Vec<int> = Vec::new();
    let mut i: usize = 0;
    while i < X_pos.len() - 1
        invariant
            i <= X_pos.len() - 1,
            y.len() == i,
            forall|k: int| 0 <= k < i as int ==> y[k] == sum(X_val@, X_crd@, v@, X_pos@[k] as int, X_pos@[k + 1] as int),
            X_crd.len() >= 1,
            X_crd.len() == X_val.len(),
            forall|k: int, l: int| 0 <= k < l < X_pos.len() ==> X_pos@[k] <= X_pos@[l],
            forall|k: int| 0 <= k < X_crd.len() ==> X_crd@[k] < v.len(),
            forall|k: int| 0 <= k < X_pos.len() ==> X_pos@[k] <= X_val.len(),
            X_pos.len() >= 1,
        decreases (X_pos.len() - 1) - i
    {
        let p1 = X_pos[i];
        let p2 = X_pos[i + 1];

        let mut yi: int = 0;
        let mut j = p1 as usize;
        while j < p2 as usize
            invariant
                p1 as usize <= j && j <= p2 as usize,
                yi == sum(X_val@, X_crd@, v@, p1 as int, j as int),
                p2 <= X_val.len(),
                X_crd.len() == X_val.len(),
                forall|k: int| 0 <= k < X_crd.len() ==> X_crd@[k] < v.len(),
            decreases (p2 as usize) - j
        {
            proof {
                sum_append_lemma(X_val@, X_crd@, v@, p1 as int, j as int);
            }
            yi = yi + X_val[j] * v[X_crd[j] as usize];
            j = j + 1;
        }

        assert(yi == sum(X_val@, X_crd@, v@, p1 as int, p2 as int));
        y.push(yi);
        i = i + 1;
    }
    y
}
// </vc-code>

}
fn main() {}