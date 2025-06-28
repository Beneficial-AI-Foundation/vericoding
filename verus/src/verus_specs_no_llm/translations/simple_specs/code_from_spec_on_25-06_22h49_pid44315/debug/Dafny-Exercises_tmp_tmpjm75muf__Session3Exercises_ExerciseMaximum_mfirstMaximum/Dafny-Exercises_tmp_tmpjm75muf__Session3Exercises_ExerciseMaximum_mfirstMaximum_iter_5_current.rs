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
            // When we find a new maximum, prove the invariants will be preserved
            assert(forall|k: int| 0 <= k <= idx ==> v.spec_index(idx as int) >= v.spec_index(k)) by {
                assert(forall|k: int| 0 <= k < idx ==> v.spec_index(max_idx as int) >= v.spec_index(k));
                assert(v.spec_index(idx as int) > v.spec_index(max_idx as int));
                assert(forall|k: int| 0 <= k < idx ==> {
                    v.spec_index(idx as int) > v.spec_index(max_idx as int) &&
                    v.spec_index(max_idx as int) >= v.spec_index(k)
                } ==> v.spec_index(idx as int) > v.spec_index(k));
                assert(v.spec_index(idx as int) >= v.spec_index(idx as int));
            };
            
            assert(forall|l: int| 0 <= l < idx ==> v.spec_index(idx as int) > v.spec_index(l)) by {
                assert(forall|l: int| 0 <= l < max_idx ==> v.spec_index(max_idx as int) > v.spec_index(l));
                assert(forall|l: int| max_idx <= l < idx ==> v.spec_index(max_idx as int) >= v.spec_index(l));
                assert(v.spec_index(idx as int) > v.spec_index(max_idx as int));
            };
            
            max_idx = idx;
        } else {
            // When we don't update max_idx, the invariants are preserved
            assert(v.spec_index(max_idx as int) >= v.spec_index(idx as int));
            assert(forall|k: int| 0 <= k <= idx ==> v.spec_index(max_idx as int) >= v.spec_index(k)) by {
                assert(forall|k: int| 0 <= k < idx ==> v.spec_index(max_idx as int) >= v.spec_index(k));
            };
        }
        idx += 1;
    }
    
    // After the loop, idx == v.len(), so prove the postconditions
    assert(idx == v.len());
    assert(0 <= max_idx < v.len());
    
    // The global maximum property follows from the loop invariant
    assert(forall|k: int| 0 <= k < v.len() ==> v.spec_index(max_idx as int) >= v.spec_index(k)) by {
        assert(forall|k: int| 0 <= k < idx ==> v.spec_index(max_idx as int) >= v.spec_index(k));
        assert(idx == v.len());
    };
    
    // The first maximum property follows from the loop invariant
    assert(forall|l: int| 0 <= l < max_idx ==> v.spec_index(max_idx as int) > v.spec_index(l)) by {
        assert(forall|l: int| 0 <= l < max_idx ==> v.spec_index(max_idx as int) > v.spec_index(l));
    };
    
    max_idx as int
}

}