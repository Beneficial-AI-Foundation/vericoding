use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u: int| 0<=u<s.len() ==> s.spec_index(u)>=0
}

fn mpositive3(v: Vec<int>) -> (b: bool)
    ensures
        b == positive(v@.subrange(0, v.len() as int))
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |u: int| 0 <= u < i ==> v@.spec_index(u) >= 0,
    {
        if v[i] < 0 {
            // Found a negative element, so the sequence is not positive
            assert(!positive(v@.subrange(0, v.len() as int))) by {
                // The negative element at index i witnesses that the sequence is not positive
                let seq = v@.subrange(0, v.len() as int);
                assert(seq == v@);
                assert(0 <= i < v.len());
                assert(i < seq.len());
                assert(seq.spec_index(i as int) == v@.spec_index(i as int));
                assert(seq.spec_index(i as int) < 0);
                // This contradicts the definition of positive
                assert(exists |u: int| 0 <= u < seq.len() && seq.spec_index(u) < 0);
            }
            return false;
        }
        i += 1;
    }
    
    // All elements are non-negative, prove the sequence is positive
    assert(positive(v@.subrange(0, v.len() as int))) by {
        let seq = v@.subrange(0, v.len() as int);
        assert(seq == v@);
        assert(seq.len() == v.len());
        
        // From the loop invariant, we know all elements up to i (which is now v.len()) are non-negative
        assert(i == v.len());
        assert(forall |u: int| 0 <= u < i ==> v@.spec_index(u) >= 0);
        assert(forall |u: int| 0 <= u < v.len() ==> v@.spec_index(u) >= 0);
        
        // Since seq == v@, this means all elements in seq are non-negative
        assert(forall |u: int| 0 <= u < seq.len() ==> seq.spec_index(u) >= 0);
    }
    return true;
}

}