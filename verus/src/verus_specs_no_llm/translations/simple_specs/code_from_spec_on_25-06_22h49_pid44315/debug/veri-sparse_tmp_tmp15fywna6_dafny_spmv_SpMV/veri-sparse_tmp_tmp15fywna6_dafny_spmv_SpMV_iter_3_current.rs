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
        // Establish bounds for this iteration
        assert(row < X_pos.len() - 1);
        assert(row + 1 < X_pos.len());
        
        let start_pos = X_pos[row] as usize;
        let end_pos = X_pos[row + 1] as usize;
        
        // Prove bounds
        assert(X_pos.spec_index(row) <= X_pos.spec_index(row + 1));
        assert(X_pos.spec_index(row + 1) <= X_val.len());
        assert(start_pos <= end_pos);
        assert(end_pos <= X_val.len());
        
        let mut row_sum = 0;
        let mut j = start_pos;
        
        while j < end_pos
            invariant
                start_pos <= j <= end_pos,
                j <= X_val.len(),
                j <= X_crd.len(),
                row_sum == sum(X_val, X_crd, v, start_pos as nat, j as nat),
                start_pos == X_pos.spec_index(row),
                end_pos == X_pos.spec_index(row + 1),
                row < X_pos.len() - 1,
                row + 1 < X_pos.len()
            decreases end_pos - j
        {
            // Prove bounds for array accesses
            assert(j < end_pos);
            assert(j < X_val.len());
            assert(j < X_crd.len());
            
            // Prove column index is valid
            assert(0 <= j < X_crd.len());
            assert(X_crd.spec_index(j) < v.len());
            
            let col_idx = X_crd[j] as usize;
            assert(col_idx < v.len());
            
            // Update sum with proof
            let old_sum = row_sum;
            row_sum = row_sum + X_val[j] * v[col_idx];
            
            // Prove the sum relationship
            assert(row_sum == old_sum + X_val.spec_index(j) * v.spec_index(X_crd.spec_index(j)));
            assert(row_sum == sum(X_val, X_crd, v, start_pos as nat, j as nat) + X_val.spec_index(j) * v.spec_index(X_crd.spec_index(j)));
            
            j = j + 1;
            
            // Prove the updated sum
            assert(row_sum == sum(X_val, X_crd, v, start_pos as nat, j as nat));
        }
        
        // Final proof that row_sum equals the expected sum
        assert(j == end_pos);
        assert(row_sum == sum(X_val, X_crd, v, start_pos as nat, end_pos as nat));
        assert(row_sum == sum(X_val, X_crd, v, X_pos.spec_index(row), X_pos.spec_index(row + 1)));
        
        y.push(row_sum);
        
        // Prove the invariant is maintained
        assert(y.len() == row + 1);
        assert(forall i :: 0 <= i < row ==> y.spec_index(i) == sum(X_val, X_crd, v, X_pos.spec_index(i), X_pos.spec_index(i + 1)));
        assert(y.spec_index(row) == sum(X_val, X_crd, v, X_pos.spec_index(row), X_pos.spec_index(row + 1)));
        
        row = row + 1;
    }
    
    y
}

}