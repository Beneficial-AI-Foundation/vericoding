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
proof fn sum_range_non_negative(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int)
    requires
        b <= k,
        forall|i: int| b <= i < k ==> X_val[i] >= 0,
        forall|i: int| b <= i < k ==> v[X_crd[i] as int] >= 0,
    ensures
        sum(X_val, X_crd, v, b, k) >= 0,
    decreases k - b
{
    if k <= b {
        assert(sum(X_val, X_crd, v, b, k) == 0);
    } else {
        sum_range_non_negative(X_val, X_crd, v, b + 1, k);
        assert(sum(X_val, X_crd, v, b, k) == sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b] as int]);
        assert(X_val[b] >= 0);
        assert(v[X_crd[b] as int] >= 0);
        assert(X_val[b] * v[X_crd[b] as int] >= 0);
        assert(sum(X_val, X_crd, v, b + 1, k) >= 0);
        assert(sum(X_val, X_crd, v, b, k) >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
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
{
    let mut y = Vec::new();
    let mut i: usize = 0;

    while i < X_pos.len() - 1
        invariant
            0 <= i < X_pos.len(),
            y.len() == i,
            forall|j: int| 0 <= j < i ==> y[j] == sum(X_val@, X_crd@, v@, X_pos[j] as int, X_pos[j + 1] as int),
    {
        let start = X_pos[i];
        let end = X_pos[i + 1];
        let mut sum_val = 0;
        let mut k: usize = start;

        while k < end
            invariant
                start <= k <= end,
                sum_val == sum(X_val@, X_crd@, v@, start as int, k as int),
                X_pos[i] == start,
                X_pos[i + 1] == end,
        {
            sum_val = sum_val + X_val[k] * v[X_crd[k]];
            k = k + 1;
        }

        y.push(sum_val);
        i = i + 1;
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