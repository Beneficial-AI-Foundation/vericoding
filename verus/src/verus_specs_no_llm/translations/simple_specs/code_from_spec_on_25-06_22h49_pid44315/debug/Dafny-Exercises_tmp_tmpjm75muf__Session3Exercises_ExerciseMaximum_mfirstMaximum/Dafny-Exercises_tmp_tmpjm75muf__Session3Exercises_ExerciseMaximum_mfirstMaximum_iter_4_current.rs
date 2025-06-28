use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mfirstMaximum(v: Vec<int>) -> (i: int)
    requires
        v.len()>0
    ensures
        0<=i<v.len(),
        forall|k: int| 0<=k<v.len() ==> v.spec_index(i)>=v.spec_index(k),
        forall|l: int| 0<=l<i ==> v.spec_index(i)>v.spec_index(l)
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
            // Prove that when we update max_idx, the invariant is preserved
            assert(forall|k: int| 0 <= k < idx ==> v.spec_index(idx as int) >= v.spec_index(k)) by {
                // v[idx] > v[max_idx] and v[max_idx] >= all elements in [0, idx)
                // Therefore v[idx] > all elements in [0, idx)
                assert(forall|k: int| 0 <= k < idx ==> {
                    v.spec_index(max_idx as int) >= v.spec_index(k) &&
                    v.spec_index(idx as int) > v.spec_index(max_idx as int)
                });
            };
            max_idx = idx;
        } else {
            // When we don't update max_idx, we need to show the invariants still hold
            assert(v.spec_index(max_idx as int) >= v.spec_index(idx as int));
        }
        idx += 1;
    }
    
    // After the loop, prove the postconditions
    assert(idx == v.len());
    
    // Prove the global maximum property
    assert(forall|k: int| 0 <= k < v.len() ==> v.spec_index(max_idx as int) >= v.spec_index(k)) by {
        // This follows from the loop invariant since idx == v.len()
    };
    
    // Prove the first maximum property  
    assert(forall|l: int| 0 <= l < max_idx ==> v.spec_index(max_idx as int) > v.spec_index(l)) by {
        // This follows directly from the loop invariant
    };
    
    max_idx as int
}

}