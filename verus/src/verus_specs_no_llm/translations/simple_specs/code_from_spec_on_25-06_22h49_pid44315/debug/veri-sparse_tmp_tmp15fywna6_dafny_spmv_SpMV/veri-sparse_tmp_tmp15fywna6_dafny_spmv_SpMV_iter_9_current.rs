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

// Helper lemma to prove sum properties
proof fn lemma_sum_extend(X_val: Vec<int>, X_crd: Vec<nat>, v: Vec<int>, start: nat, end: nat)
    requires
        start < end,
        end <= X_val.len(),
        end <= X_crd.len(),
        forall i: nat :: start <= i < end ==> X_crd.spec_index(i) < v.len()
    ensures
        sum(X_val, X_crd, v, start, end) == 
        sum(X_val, X_crd, v, start, end - 1) + X_val.spec_index(end - 1) * v.spec_index(X_crd.spec_index(end - 1))
    decreases end - start
{
    if start + 1 == end {
        // Base case: sum from start to start+1
        assert(sum(X_val, X_crd, v, start, end - 1) == 0);
        assert(sum(X_val, X_crd, v, start, end) == X_val.spec_index(start) * v.spec_index(X_crd.spec_index(start)));
    } else {
        // Recursive case
        lemma_sum_extend(X_val, X_crd, v, start + 1, end);
    }
}

fn SpMV(X_val: Vec<int>, X_crd: Vec<nat>, X_pos: Vec<nat>, v: Vec<int>) -> (y: Vec<int>)
    requires
        X_crd.len() >= 1,
        X_crd.len() == X_val.len(),
        forall i: int, j: int :: 0 <= i < j < X_pos.len() ==> X_pos.spec_index(i) <= X_pos.spec_index(j),
        forall i: nat :: 0 <= i < X_crd.len() ==> X_crd.spec_index(i) < v.len(),
        forall i: nat :: 0 <= i < X_pos.len() ==> X_pos.spec_index(i) <= X_val.len(),
        X_pos.len() >= 1
    ensures
        y.len() + 1 == X_pos.len(),
        forall i: nat :: 0 <= i < y.len() ==> y.spec_index(i) == sum(X_val, X_crd, v, X_pos.spec_index(i), X_pos.spec_index(i + 1))
{
    let mut y = Vec::new();
    let mut row = 0usize;
    
    while row < X_pos.len() - 1
        invariant
            row <= X_pos.len() - 1,
            y.len() == row,
            forall i: nat :: 0 <= i < y.len() ==> y.spec_index(i) == sum(X_val, X_crd, v, X_pos.spec_index(i), X_pos.spec_index(i + 1)),
            X_pos.len() >= 1,
            forall i: nat :: 0 <= i < X_pos.len() ==> X_pos.spec_index(i) <= X_val.len(),
            forall i: nat :: 0 <= i < X_crd.len() ==> X_crd.spec_index(i) < v.len(),
            X_crd.len() == X_val.len(),
            forall i: int, j: int :: 0 <= i < j < X_pos.len() ==> X_pos.spec_index(i) <= X_pos.spec_index(j)
    {
        // Establish basic bounds
        assert(row < X_pos.len());
        assert(row + 1 < X_pos.len());
        
        let start_pos = X_pos[row] as usize;
        let end_pos = X_pos[row + 1] as usize;
        
        // Establish ordering and bounds
        assert(X_pos.spec_index(row) <= X_pos.spec_index(row + 1)) by {
            assert(0 <= row < row + 1 < X_pos.len());
        }
        assert(start_pos <= end_pos);
        assert(end_pos <= X_val.len());
        assert(end_pos <= X_crd.len());
        
        // Establish that all indices in range are valid
        assert(forall k: nat :: start_pos <= k < end_pos ==> k < X_crd.len() && X_crd.spec_index(k) < v.len()) by {
            assert(forall k: nat :: start_pos <= k < end_pos ==> k < X_val.len());
            assert(X_crd.len() == X_val.len());
        }
        
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
                row + 1 < X_pos.len(),
                forall k: nat :: start_pos <= k < end_pos ==> k < X_crd.len() && X_crd.spec_index(k) < v.len(),
                X_crd.len() == X_val.len(),
                end_pos <= X_val.len(),
                forall k: nat :: start_pos <= k < end_pos ==> k < X_val.len()
            decreases end_pos - j
        {
            // Establish bounds for current access
            assert(j < end_pos);
            assert(j < X_val.len());
            assert(j < X_crd.len());
            assert(X_crd.spec_index(j as nat) < v.len());
            
            let col_idx = X_crd[j] as usize;
            assert(col_idx < v.len());
            
            let old_sum = row_sum;
            row_sum = row_sum + X_val[j] * v[col_idx];
            
            // Prove the sum relationship using the lemma
            assert(j as nat + 1 <= end_pos as nat);
            assert(j as nat + 1 <= X_val.len() as nat);
            assert(j as nat + 1 <= X_crd.len() as nat);
            assert(forall k: nat :: start_pos as nat <= k < j as nat + 1 ==> X_crd.spec_index(k) < v.len());
            
            lemma_sum_extend(X_val, X_crd, v, start_pos as nat, (j + 1) as nat);
            
            assert(sum(X_val, X_crd, v, start_pos as nat, (j + 1) as nat) == 
                   sum(X_val, X_crd, v, start_pos as nat, j as nat) + 
                   X_val.spec_index(j as nat) * v.spec_index(X_crd.spec_index(j as nat)));
            
            assert(old_sum == sum(X_val, X_crd, v, start_pos as nat, j as nat));
            assert(X_val[j] == X_val.spec_index(j as nat));
            assert(v[col_idx] == v.spec_index(X_crd.spec_index(j as nat)));
            assert(row_sum == sum(X_val, X_crd, v, start_pos as nat, (j + 1) as nat));
            
            j = j + 1;
        }
        
        // Final assertion that row_sum equals the desired sum
        assert(j == end_pos);
        assert(row_sum == sum(X_val, X_crd, v, X_pos.spec_index(row), X_pos.spec_index(row + 1)));
        
        y.push(row_sum);
        row = row + 1;
    }
    
    y
}

}