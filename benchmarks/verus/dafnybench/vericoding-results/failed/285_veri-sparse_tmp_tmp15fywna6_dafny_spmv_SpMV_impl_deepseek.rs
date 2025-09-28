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
proof fn lemma_sum_recursive(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int)
    requires
        b < k,
        0 <= b < X_val.len() as int,
        0 <= X_crd[b] as int < v.len() as int,
    ensures
        sum(X_val, X_crd, v, b, k) == X_val[b] * v[X_crd[b] as int] + sum(X_val, X_crd, v, b + 1, k)
{
    reveal_with_fuel(sum, 2);
}

proof fn lemma_sum_base(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, k: int)
    ensures
        sum(X_val, X_crd, v, k, k) == 0
{
    reveal_with_fuel(sum, 1);
}

proof fn lemma_sum_range_empty(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int)
    ensures
        sum(X_val, X_crd, v, b, b) == 0
{
    reveal_with_fuel(sum, 1);
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
    let mut i = 0;
    while i < X_pos.len() - 1
        invariant
            0 <= i <= X_pos.len() - 1,
            y.len() == i,
            forall|j: int| 0 <= j < i ==> y@[j] == sum(X_val@, X_crd@, v@, X_pos[j] as int, X_pos[j + 1] as int),
    {
        let start_idx = X_pos[i] as usize;
        let end_idx = X_pos[i + 1] as usize;
        let mut sum_val = 0;
        let mut idx = start_idx;
        
        proof {
            lemma_sum_range_empty(X_val@, X_crd@, v@, start_idx as int);
        }
        
        while idx < end_idx
            invariant
                start_idx <= idx <= end_idx,
                sum_val == sum(X_val@, X_crd@, v@, start_idx as int, idx as int),
        {
            let col = X_crd[idx] as usize;
            sum_val = sum_val + X_val[idx] * v[col];
            idx = idx + 1;
            
            proof {
                if (idx - 1) < X_crd.len() {
                    lemma_sum_recursive(X_val@, X_crd@, v@, (idx - 1) as int, end_idx as int);
                }
            }
        }
        
        proof {
            lemma_sum_base(X_val@, X_crd@, v@, end_idx as int);
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