use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn allEqual(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s.spec_index(i) == s.spec_index(j)
}

fn mallEqual3(v: Vec<int>) -> (b: bool)
    ensures
        b == allEqual(v@)
{
    if v.len() == 0 {
        // Empty sequence satisfies allEqual vacuously
        return true;
    }
    
    let first = v[0];
    let mut i = 1;
    
    while i < v.len()
        invariant
            0 < i <= v.len(),
            v.len() > 0,
            forall|k: int| 0 <= k < i ==> v@.spec_index(k) == first,
    {
        if v[i] != first {
            // We found elements that are different
            // Since elements at index 0 and i are different, allEqual is false
            assert(v@.spec_index(0) == first);
            assert(v@.spec_index(i as int) == v[i]);
            assert(v[i] != first);
            assert(v@.spec_index(0) != v@.spec_index(i as int));
            assert(!allEqual(v@)) by {
                // Witness that allEqual is false
                assert(0 <= 0 < v@.len() && 0 <= i < v@.len());
                assert(v@.spec_index(0) != v@.spec_index(i as int));
            };
            return false;
        }
        i += 1;
    }
    
    // At this point, all elements are equal to first
    assert(forall|k: int| 0 <= k < v.len() ==> v@.spec_index(k) == first);
    
    // Prove allEqual(v@) by showing all pairs of elements are equal
    assert(allEqual(v@)) by {
        assert(forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> {
            &&& v@.spec_index(i) == first
            &&& v@.spec_index(j) == first
            &&& v@.spec_index(i) == v@.spec_index(j)
        });
    };
    
    true
}

}