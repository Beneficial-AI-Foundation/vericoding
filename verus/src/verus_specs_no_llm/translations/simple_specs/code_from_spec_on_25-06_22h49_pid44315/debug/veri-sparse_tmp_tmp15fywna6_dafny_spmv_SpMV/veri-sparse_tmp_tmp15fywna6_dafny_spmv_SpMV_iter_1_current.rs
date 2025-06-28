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
    let mut row = 0;
    
    while row < X_pos.len() - 1
        invariant
            row <= X_pos.len() - 1,
            y.len() == row,
            forall i :: 0 <= i < y.len() ==> y.spec_index(i) == sum(X_val, X_crd, v, X_pos.spec_index(i), X_pos.spec_index(i + 1))
    {
        let start_pos = X_pos[row];
        let end_pos = X_pos[row + 1];
        let mut row_sum = 0;
        let mut j = start_pos;
        
        while j < end_pos
            invariant
                start_pos <= j <= end_pos,
                j <= X_val.len(),
                row_sum == sum(X_val, X_crd, v, start_pos, j)
            decreases end_pos - j
        {
            row_sum = row_sum + X_val[j] * v[X_crd[j]];
            j = j + 1;
        }
        
        y.push(row_sum);
        row = row + 1;
    }
    
    y
}

}

The key insights for this implementation:


   - Iterate through each row (from 0 to `X_pos.len() - 1`)
   - For each row, compute the sum from `X_pos[row]` to `X_pos[row+1]`
   - Use nested loops with appropriate invariants to prove correctness

   - Outer loop maintains that we've processed `row` rows correctly
   - Inner loop maintains that we've computed the partial sum correctly up to index `j`


This implementation satisfies all the original constraints while providing a verified sparse matrix-vector multiplication function.