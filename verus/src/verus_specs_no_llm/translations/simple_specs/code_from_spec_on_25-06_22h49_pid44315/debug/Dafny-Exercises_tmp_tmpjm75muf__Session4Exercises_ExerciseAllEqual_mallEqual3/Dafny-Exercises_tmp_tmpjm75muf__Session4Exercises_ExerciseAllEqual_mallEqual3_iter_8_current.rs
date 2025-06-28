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
        return true;
    }
    
    let first = v[0];
    let mut i = 1;
    
    while i < v.len()
        invariant
            0 < i <= v.len(),
            v.len() > 0,
            forall|k: int| 0 <= k < i ==> v@.spec_index(k) == first,
            v@.spec_index(0) == first,
    {
        if v[i] != first {
            // Need to prove that allEqual(v@) is false when we find different elements
            assert(v@.spec_index(0) == first);
            assert(v@.spec_index(i as int) != first);
            assert(!allEqual(v@));
            return false;
        }
        i += 1;
    }
    
    // Need to prove that allEqual(v@) is true when all elements are equal to first
    assert(forall|k: int| 0 <= k < v.len() ==> v@.spec_index(k) == first);
    assert(forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> {
        v@.spec_index(i) == first && v@.spec_index(j) == first
    });
    assert(forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> {
        v@.spec_index(i) == v@.spec_index(j)
    });
    assert(allEqual(v@));
    
    true
}

}