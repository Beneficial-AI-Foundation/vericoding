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
proof fn sum_empty(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int)
    ensures sum(X_val, X_crd, v, b, b) == 0
{
}

proof fn sum_extend(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int)
    requires b < k
    ensures sum(X_val, X_crd, v, b, k) == X_val[b] * v[X_crd[b] as int] + sum(X_val, X_crd, v, b + 1, k)
{
}

proof fn sum_single(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int)
    ensures sum(X_val, X_crd, v, b, b + 1) == X_val[b] * v[X_crd[b] as int]
{
    sum_empty(X_val, X_crd, v, b + 1);
}

proof fn sum_range_valid(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int, crd_len: int, v_len: int)
    requires 
        b <= k,
        forall|i: int| 0 <= i < crd_len ==> X_crd[i] < v_len,
        0 <= b < crd_len,
        k <= crd_len
    ensures sum(X_val, X_crd, v, b, k) == sum(X_val, X_crd, v, b, k)
{
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
{
    let mut y = Vec::new();
    let mut i: usize = 0;
    
    while i + 1 < X_pos.len()
        invariant
            i <= X_pos.len(),
            y.len() == i,
            forall|j: int| 0 <= j < i ==> y[j] == sum(X_val@, X_crd@, v@, X_pos@[j] as int, X_pos@[j + 1] as int),
    {
        let ghost start = X_pos@[i as int];
        let ghost end = X_pos@[i as int + 1];
        
        let mut row_sum: int = 0int;
        let mut k: usize = X_pos[i] as usize;
        
        while k < X_pos[i + 1] as usize
            invariant
                X_pos[i] as usize <= k <= X_pos[i + 1] as usize,
                X_pos[i + 1] <= X_val.len(),
                row_sum == sum(X_val@, X_crd@, v@, X_pos@[i as int] as int, k as int),
                forall|j: int| X_pos@[i as int] as int <= j < k as int ==> X_crd@[j] < v.len(),
        {
            row_sum = row_sum + X_val[k] * v[X_crd[k] as usize];
            k = k + 1;
        }
        
        y.push(row_sum);
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