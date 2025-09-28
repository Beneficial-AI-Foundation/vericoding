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
proof fn sum_plus_one(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int)
    requires
        0 <= b,
        b <= k,
        k < X_val.len(),
    ensures
        sum(X_val, X_crd, v, b, k + 1) == sum(X_val, X_crd, v, b, k) + X_val[k] * v[X_crd[k] as int],
    decreases k - b
{
    if k == b {
        assert(sum(X_val, X_crd, v, b, k) == 0);
        assert(sum(X_val, X_crd, v, b, k + 1) == sum(X_val, X_crd, v, b + 1, k + 1) + X_val[b] * v[X_crd[b] as int]);
        assert(sum(X_val, X_crd, v, b + 1, k + 1) == 0);
    } else {
        sum_plus_one(X_val, X_crd, v, b + 1, k);
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
    let m: usize = X_pos.len();
    let mut y: Vec<int> = Vec::new();
    if m >= 1 {
        y.reserve(m - 1);
    }

    let m_int: int = m as int;
    let mut row: int = 0;
    while row < m_int - 1
        invariant 0 <= row && row <= m_int - 1;
        invariant y.len() == row as usize;
        invariant forall |ii: int| 0 <= ii < row ==>
            y[ii as usize] == sum(X_val@, X_crd@, v@, X_pos@[ii] as int, X_pos@[ii + 1] as int)
    {
        let start_nat: nat = X_pos[row as usize];
        let end_nat: nat = X_pos[(row + 1) as usize];
        let start_usize: usize = start_nat as usize;
        let end_usize: usize = end_nat as usize;

        let mut j: usize = start_usize;
        let mut acc: int = 0;
        assert(acc == sum(X_val@, X_crd@, v@, start_nat as int, start_nat as int));
        while j < end_usize
            invariant start_usize <= j && j <= end_usize;
            invariant acc == sum(X_val@, X_crd@, v@, start_nat as int, j as int)
        {
            let val_j: int = X_val[j];
            let crd_j: nat = X_crd[j];
            let prod: int = val_j * v[crd_j as usize];
            acc = acc + prod;

            proof {
                assert(0 <= start_nat as int);
                assert(start_nat as int <= j as int);
                assert(j < X_val.len());
                sum_plus_one(X_val@, X_crd@, v@, start_nat as int, j as int);
                assert(acc == sum(X_val@, X_crd@, v@, start_nat as int, (j + 1) as int));
            }

            j += 1;
        }
        assert(acc == sum(X_val@, X_crd@, v@, start_nat as int, end_nat as int));
        y.push(acc);
        row += 1;
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