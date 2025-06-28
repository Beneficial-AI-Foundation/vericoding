use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn maxArray(a: Vec<int>) -> (m: int)
    requires
        a.len() >= 1
    ensures
        forall|k: int| 0 <= k < a.len() ==> m >= a.spec_index(k),
        exists|k: int| 0 <= k < a.len() && m == a.spec_index(k)
{
    let mut max = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> max >= a.spec_index(k),
            exists|k: int| 0 <= k < i && max == a.spec_index(k)
    {
        if a[i] > max {
            max = a[i];
        }
        
        // Prove the invariants for the next iteration
        assert(forall|k: int| 0 <= k < (i + 1) ==> max >= a.spec_index(k)) by {
            assert(forall|k: int| 0 <= k < i ==> max >= a.spec_index(k)); // from loop invariant
            assert(max >= a.spec_index(i as int)); // current element
        };
        
        assert(exists|k: int| 0 <= k < (i + 1) && max == a.spec_index(k)) by {
            if max == a[i] {
                assert(max == a.spec_index(i as int));
            } else {
                // max didn't change, so the witness from the invariant still holds
                assert(exists|k: int| 0 <= k < i && max == a.spec_index(k));
            }
        };
        
        i = i + 1;
    }
    
    max
}

}