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
    
    // The invariants directly give us what we need for the postconditions
    // Since idx == v.len(), the invariants apply to the entire vector
    
    // First postcondition: max_idx is a valid index
    assert(0 <= max_idx as int < v.len());
    
    // Second postcondition: v[max_idx] >= v[k] for all valid k
    assert(forall |k: int| 0 <= k < v.len() ==> v.spec_index(max_idx as int) >= v.spec_index(k)) by {
        assert(max_val == v.spec_index(max_idx as int));
        assert(forall |k: int| 0 <= k < idx ==> v.spec_index(k) <= max_val);
        assert(idx == v.len());
    };
    
    // Third postcondition: v[max_idx] > v[l] for all l > max_idx
    assert(forall |l: int| (max_idx as int) < l < v.len() ==> v.spec_index(max_idx as int) > v.spec_index(l)) by {
        assert(max_val == v.spec_index(max_idx as int));
        assert(forall |l: int| (max_idx as int) < l < idx ==> v.spec_index(l) < max_val);
        assert(idx == v.len());
    };
    
    max_idx as int
}

}