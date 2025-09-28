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
spec fn sum(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int) -> int
    decreases k - b
{
    if k <= b {
        0
    } else {
        sum(X_val, X_crd, v, b + 1, k) + X_val@[b] * v@[X_crd@[b] as int]
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
{
    let n_rows: usize = X_pos.len() - 1;
    let mut y: Vec<int> = Vec::with_capacity(n_rows);
    let mut outer_idx: usize = 0;

    while outer_idx < n_rows
        invariant
            0 <= outer_idx <= n_rows,
            y@.len() == outer_idx as int,
            forall|k: int| 0 <= k < outer_idx as int ==> #[trigger] (y@[k] == sum(X_val@, X_crd@, v@, X_pos@[k] as int, X_pos@[k + 1] as int))
    {
        let start_col: usize = X_pos[outer_idx] as usize;
        let end_col: usize = X_pos[outer_idx + 1] as usize;
        let mut s: int = 0;
        let mut inner_idx: usize = start_col;

        while inner_idx < end_col
            invariant s == sum(X_val@, X_crd@, v@, start_col as int, inner_idx as int)
        {
            let val: int = X_val[inner_idx];
            let col: usize = X_crd[inner_idx] as usize;
            let vec_val: int = v[col];
            s = s + val * vec_val;
            inner_idx += 1;

            assert(s == sum(X_val@, X_crd@, v@, start_col as int, inner_idx as int));
        }

        assert(s == sum(X_val@, X_crd@, v@, start_col as int, end_col as int));
        y.push(s);

        outer_idx += 1;

        assert(y@.len() == outer_idx as int);
        assert(forall|k: int| 0 <= k < outer_idx as int ==> #[trigger] (y@[k] == sum(X_val@, X_crd@, v@, X_pos@[k] as int, X_pos@[k + 1] as int)));
    }

    y
}
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