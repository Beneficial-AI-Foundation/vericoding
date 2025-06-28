use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mmaximum2(v: Vec<int>) -> (i: int)
    requires
        v.len() > 0
    ensures
        0 <= i < v.len(),
        forall |k: int| 0 <= k < v.len() ==> v.spec_index(i) >= v.spec_index(k)
{
    let mut max_idx: usize = 0;
    let mut idx: usize = 1;
    
    while idx < v.len()
        invariant
            0 <= max_idx < v.len(),
            1 <= idx <= v.len(),
            forall |k: int| 0 <= k < idx ==> v.spec_index(max_idx as int) >= v.spec_index(k)
    {
        if v[idx] > v[max_idx] {
            max_idx = idx;
            proof {
                // Prove that the new max_idx maintains the invariant
                assert forall |k: int| 0 <= k < idx + 1 implies v.spec_index(max_idx as int) >= v.spec_index(k) by {
                    if k < idx {
                        // This follows from the loop invariant for the old max_idx and the fact that v[idx] > v[old_max_idx]
                    } else if k == idx {
                        // This is trivially true since max_idx == idx
                    }
                }
            }
        } else {
            proof {
                // Prove that keeping the old max_idx maintains the invariant
                assert forall |k: int| 0 <= k < idx + 1 implies v.spec_index(max_idx as int) >= v.spec_index(k) by {
                    if k < idx {
                        // This follows from the loop invariant
                    } else if k == idx {
                        // This follows from v[idx] <= v[max_idx]
                    }
                }
            }
        }
        idx = idx + 1;
    }
    
    proof {
        // Prove the postcondition
        assert(0 <= max_idx < v.len());
        assert(forall |k: int| 0 <= k < v.len() ==> v.spec_index(max_idx as int) >= v.spec_index(k)) by {
            // When the loop exits, idx == v.len(), so the loop invariant gives us what we need
            assert(idx == v.len());
        }
    }
    
    max_idx as int
}

}