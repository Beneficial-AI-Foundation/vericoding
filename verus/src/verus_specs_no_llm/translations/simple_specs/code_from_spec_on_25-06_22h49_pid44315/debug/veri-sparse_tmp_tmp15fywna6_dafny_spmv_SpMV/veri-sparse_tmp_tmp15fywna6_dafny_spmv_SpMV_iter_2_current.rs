use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(X_val: Vec<int>, X_crd: Vec<nat>, v: Vec<int>, start: nat, end: nat) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        X_val.spec_index(start) * v.spec_index(X_crd.spec_index(start)) + sum(X_val, X_crd, v, start + 1, end)
    }
}

fn SpMV(X_val: Vec<int>, X_crd: Vec<nat>, X_pos: Vec<nat>, v: Vec<int>) -> (y: Vec<int>)
    requires
        X_crd.len() >= 1,
        X_crd.len() == X_val.len(),
        forall i, j :: 0 <= i < j < X_pos.len() ==> X_pos.spec_index(i) <= X_pos.spec_index(j),
        forall i :: 0 <= i < X_crd.len() ==> X_crd.spec_index(i) < v.len(),
        forall i :: 0 <= i < X_pos.len() ==> X_pos.spec_index(i) <= X_val.len(),
        X_pos.len() >= 1
    ensures
        y.len() + 1 == X_pos.len(),
        forall i :: 0 <= i < y.len() ==> y.spec_index(i) == sum(X_val, X_crd, v, X_pos.spec_index(i), X_pos.spec_index(i + 1))
{
    let mut y = Vec::new();
    let mut row = 0usize;
    
    while row < X_pos.len() - 1
        invariant
            row <= X_pos.len() - 1,
            y.len() == row,
            forall i :: 0 <= i < y.len() ==> y.spec_index(i) == sum(X_val, X_crd, v, X_pos.spec_index(i), X_pos.spec_index(i + 1))
    {
        let start_pos = X_pos[row] as usize;
        let end_pos = X_pos[row + 1] as usize;
        let mut row_sum = 0;
        let mut j = start_pos;
        
        // Prove bounds for the inner loop
        assert(X_pos.spec_index(row) <= X_pos.spec_index(row + 1));
        assert(X_pos.spec_index(row + 1) <= X_val.len());
        
        while j < end_pos
            invariant
                start_pos <= j <= end_pos,
                j <= X_val.len(),
                row_sum == sum(X_val, X_crd, v, X_pos.spec_index(row), j as nat),
                start_pos == X_pos.spec_index(row),
                end_pos == X_pos.spec_index(row + 1),
                forall k :: start_pos <= k < j ==> X_crd.spec_index(k) < v.len()
            decreases end_pos - j
        {
            // Prove bounds for array accesses
            assert(j < X_val.len());
            assert(j < X_crd.len());
            assert(X_crd.spec_index(j) < v.len());
            
            let col_idx = X_crd[j] as usize;
            row_sum = row_sum + X_val[j] * v[col_idx];
            j = j + 1;
        }
        
        // Prove the final sum is correct
        assert(row_sum == sum(X_val, X_crd, v, X_pos.spec_index(row), X_pos.spec_index(row + 1)));
        
        y.push(row_sum);
        row = row + 1;
    }
    
    y
}

}