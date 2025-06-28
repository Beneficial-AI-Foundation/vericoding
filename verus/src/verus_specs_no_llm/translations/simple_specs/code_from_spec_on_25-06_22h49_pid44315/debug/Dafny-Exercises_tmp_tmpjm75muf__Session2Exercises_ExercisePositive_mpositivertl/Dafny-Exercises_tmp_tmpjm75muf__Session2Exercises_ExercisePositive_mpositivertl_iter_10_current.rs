use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s.spec_index(u) >= 0
}

fn mpositivertl(v: Vec<int>) -> (b: bool)
    ensures
        b == positive(v@.subrange(0, v.len() as int))
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|u: int| 0 <= u < i ==> v@.spec_index(u) >= 0
    {
        if v[i] < 0 {
            // Prove that the postcondition holds when returning false
            proof {
                // Show that the negative element exists in the subrange
                assert(v@.spec_index(i as int) < 0);
                assert(0 <= i < v.len());
                
                // Key insight: subrange(0, v.len()) is the same as the full sequence
                assert(v@.subrange(0, v.len() as int) =~= v@);
                
                // Since we found a negative element at position i, positive is false
                assert(!positive(v@.subrange(0, v.len() as int))) by {
                    assert(0 <= i < v@.subrange(0, v.len() as int).len());
                    assert(v@.subrange(0, v.len() as int).spec_index(i as int) < 0);
                }
            }
            return false;
        }
        i += 1;
    }
    
    // At this point, all elements are non-negative
    proof {
        // From the loop invariant with i == v.len()
        assert(i == v.len());
        assert(forall|u: int| 0 <= u < i ==> v@.spec_index(u) >= 0);
        
        // This means all elements in the vector are non-negative
        assert(forall|u: int| 0 <= u < v@.len() ==> v@.spec_index(u) >= 0);
        
        // subrange(0, v.len()) equals the full sequence
        assert(v@.subrange(0, v.len() as int) =~= v@);
        
        // Therefore positive holds for the subrange
        assert(positive(v@.subrange(0, v.len() as int))) by {
            assert(forall|u: int| 0 <= u < v@.subrange(0, v.len() as int).len() ==> 
                v@.subrange(0, v.len() as int).spec_index(u) >= 0);
        }
    }
    
    true
}

}