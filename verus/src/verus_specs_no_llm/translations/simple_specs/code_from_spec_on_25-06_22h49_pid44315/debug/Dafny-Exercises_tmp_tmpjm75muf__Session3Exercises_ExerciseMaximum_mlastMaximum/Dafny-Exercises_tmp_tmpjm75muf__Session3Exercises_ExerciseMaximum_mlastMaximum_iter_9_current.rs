use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mlastMaximum(v: Vec<int>) -> (i: int)
    requires
        v.len() > 0
    ensures
        0 <= i < v.len(),
        forall |k: int| 0 <= k < v.len() ==> v.spec_index(i) >= v.spec_index(k),
        forall |l: int| i < l < v.len() ==> v.spec_index(i) > v.spec_index(l)
{
    let mut max_val = v[0];
    let mut max_idx: usize = 0;
    let mut idx: usize = 1;
    
    while idx < v.len()
        invariant
            0 <= max_idx < v.len(),
            1 <= idx <= v.len(),
            max_val == v.spec_index(max_idx as int),
            // max_val is the maximum among elements seen so far
            forall |k: int| 0 <= k < idx ==> v.spec_index(k) <= max_val,
            // max_idx is the last occurrence of max_val among elements seen so far
            forall |k: int| 0 <= k < idx && v.spec_index(k) == max_val ==> k <= max_idx as int,
            // elements after max_idx (among those seen so far) are strictly less than max_val
            forall |l: int| (max_idx as int) < l < idx ==> v.spec_index(l) < max_val,
    {
        if v[idx] >= max_val {
            max_val = v[idx];
            max_idx = idx;
        }
        idx += 1;
    }
    
    // After the loop, idx == v.len(), so we've seen all elements
    assert(idx == v.len());
    
    // Prove the postconditions
    assert(forall |k: int| 0 <= k < v.len() ==> v.spec_index(max_idx as int) >= v.spec_index(k)) by {
        // From invariant: max_val == v.spec_index(max_idx as int)
        // From invariant: forall k:: 0 <= k < idx ==> v.spec_index(k) <= max_val
        // Since idx == v.len(), this covers all elements
    };
    
    assert(forall |l: int| (max_idx as int) < l < v.len() ==> v.spec_index(max_idx as int) > v.spec_index(l)) by {
        // From invariant: forall l:: max_idx < l < idx ==> v.spec_index(l) < max_val
        // From invariant: max_val == v.spec_index(max_idx as int)
        // Since idx == v.len(), this covers the required range
    };
    
    max_idx as int
}

}