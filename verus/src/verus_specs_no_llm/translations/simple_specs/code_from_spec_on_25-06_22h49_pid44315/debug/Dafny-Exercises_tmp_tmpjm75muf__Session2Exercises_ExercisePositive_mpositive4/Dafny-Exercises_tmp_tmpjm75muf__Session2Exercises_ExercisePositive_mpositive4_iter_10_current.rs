use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u: int| 0<=u<s.len() ==> s.spec_index(u)>=0
}

fn mpositive4(v: Vec<int>) -> (b: bool)
    ensures
        b==positive(v@)
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |u: int| 0<=u<(i as int) ==> v@.spec_index(u)>=0
        decreases v.len() - i
    {
        if v[i] < 0 {
            assert(!positive(v@)) by {
                // We found a negative element at position i
                assert(v@.spec_index(i as int) < 0);
                assert(0 <= (i as int) < v@.len());
                // This directly contradicts the positive property
                // positive(v@) requires ALL elements to be >= 0
                // But we have v@.spec_index(i as int) < 0
                // Therefore positive(v@) must be false
            }
            return false;
        }
        i += 1;
    }
    
    assert(positive(v@)) by {
        // After the loop, i == v.len()
        assert(i == v.len());
        // From the loop invariant, we know all elements from 0 to i-1 are >= 0
        assert(forall |u: int| 0<=u<(i as int) ==> v@.spec_index(u)>=0);
        // Since i == v.len(), this means all elements in the vector are >= 0
        assert((i as int) == v@.len());
    }
    
    true
}

}