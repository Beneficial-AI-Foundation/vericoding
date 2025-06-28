use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mfirstMaximum(v: Vec<int>) -> (i: int)
    requires
        v.len() > 0
    ensures
        0 <= i < v.len(),
        forall|k: int| 0 <= k < v.len() ==> v.spec_index(i) >= v.spec_index(k),
        forall|l: int| 0 <= l < i ==> v.spec_index(i) > v.spec_index(l)
//Algorithm: from left to right
{
    let mut max_idx: usize = 0;
    let mut idx: usize = 1;
    
    while idx < v.len()
        invariant
            0 <= max_idx < v.len(),
            1 <= idx <= v.len(),
            max_idx < idx,
            forall|k: int| 0 <= k < idx ==> v.spec_index(max_idx as int) >= v.spec_index(k),
            forall|l: int| 0 <= l < max_idx ==> v.spec_index(max_idx as int) > v.spec_index(l)
    {
        if v[idx] > v[max_idx] {
            max_idx = idx;
        } else if v[idx] == v[max_idx] {
            // Don't update max_idx to maintain leftmost property
        }
        idx += 1;
    }
    
    // Proof that the postcondition holds
    assert(forall|k: int| 0 <= k < v.len() ==> v.spec_index(max_idx as int) >= v.spec_index(k)) by {
        assert(forall|k: int| 0 <= k < idx ==> v.spec_index(max_idx as int) >= v.spec_index(k));
        assert(idx == v.len());
    };
    
    assert(forall|l: int| 0 <= l < max_idx ==> v.spec_index(max_idx as int) > v.spec_index(l));
    
    max_idx as int
}

}