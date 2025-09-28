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
proof fn sum_step(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int)
    requires
        b < k,
        b >= 0,
        b < X_val.len(),
        b < X_crd.len(),
        X_crd[b] < v.len(),
    ensures
        sum(X_val, X_crd, v, b, k) == X_val[b] * v[X_crd[b] as int] + sum(X_val, X_crd, v, b + 1, k),
{
    reveal(sum);
}

proof fn sum_empty(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int)
    ensures sum(X_val, X_crd, v, b, b) == 0
{
    reveal(sum);
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
    let mut y = Vec::new();
    let mut i: usize = 0;
    
    while i < X_pos.len() - 1
        invariant
            i <= X_pos.len() - 1,
            y.len() == i,
            forall|j: int| 0 <= j < i ==> y[j] == sum(X_val@, X_crd@, v@, X_pos[j] as int, X_pos[j + 1] as int),
    {
        let start = X_pos[i] as int as usize;
        let end = X_pos[i + 1] as int as usize;
        
        let mut row_sum: int = 0int;
        let mut j: usize = start;
        
        while j < end
            invariant
                start <= j <= end,
                end <= X_val.len(),
                end <= X_crd.len(),
                row_sum == sum(X_val@, X_crd@, v@, start as int, j as int),
                forall|k: int| start as int <= k < j as int ==> k < X_crd.len(),
                forall|k: int| start as int <= k < j as int ==> X_crd[k] < v.len(),
        {
            assert(j < X_crd.len());
            assert(X_crd[j] as int < v.len() as int);
            
            proof {
                sum_step(X_val@, X_crd@, v@, j as int, end as int);
            }
            
            let x_val_j = X_val[j];
            let x_crd_j = X_crd[j] as int as usize;
            let v_val = v[x_crd_j];
            row_sum = row_sum + x_val_j * v_val;
            j = j + 1;
        }
        
        assert(row_sum == sum(X_val@, X_crd@, v@, start as int, end as int));
        assert(row_sum == sum(X_val@, X_crd@, v@, X_pos[i as int] as int, X_pos[i + 1 as int] as int));
        
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