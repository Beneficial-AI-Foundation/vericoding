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
                assert(v@.spec_index(i as int) < 0);
                assert(0 <= i < v.len());
                assert(v@.subrange(0, v.len() as int).spec_index(i as int) == v@.spec_index(i as int));
            };
            return false;
        }
        i += 1;
    }
    
    // All elements are non-negative, prove the sequence is positive
    assert(positive(v@.subrange(0, v.len() as int))) by {
        assert(forall |u: int| 0 <= u < v.len() ==> v@.spec_index(u) >= 0);
        assert(v@.subrange(0, v.len() as int).len() == v.len());
        assert(forall |u: int| 0 <= u < v@.subrange(0, v.len() as int).len() ==> 
               v@.subrange(0, v.len() as int).spec_index(u) == v@.spec_index(u));
    };
    return true;
}

}