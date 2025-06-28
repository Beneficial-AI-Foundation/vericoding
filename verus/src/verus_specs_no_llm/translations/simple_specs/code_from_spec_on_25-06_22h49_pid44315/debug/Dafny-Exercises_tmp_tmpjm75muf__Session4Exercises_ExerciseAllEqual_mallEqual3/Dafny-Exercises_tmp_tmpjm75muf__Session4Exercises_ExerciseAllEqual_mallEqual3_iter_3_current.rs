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
            0 <= i <= v.len(),
            forall|k: int| 0 <= k < i ==> v@.spec_index(k) == first,
            v@.spec_index(0) == first,
    {
        if v[i] != first {
            // Prove that not all elements are equal when we find a mismatch
            assert(v@.spec_index(0) == first);
            assert(v@.spec_index(i as int) != first);
            // Use the fact that we have two different values to prove allEqual is false
            assert(0 <= 0 < v@.len() && 0 <= i < v@.len());
            assert(v@.spec_index(0) != v@.spec_index(i as int));
            assert(exists|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() && v@.spec_index(x) != v@.spec_index(y));
            assert(!allEqual(v@));
            return false;
        }
        i += 1;
    }
    
    // Prove that all elements are equal when we exit the loop
    assert(forall|k: int| 0 <= k < v.len() ==> v@.spec_index(k) == first);
    
    // Now prove allEqual by showing any two indices have equal values
    assert(forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> {
        v@.spec_index(i) == first && v@.spec_index(j) == first
    }) by {
        // The proof follows from the invariant we maintained
    };
    
    assert(forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> 
        v@.spec_index(i) == v@.spec_index(j)) by {
        // Since both equal first, they equal each other
    };
    
    assert(allEqual(v@));
    
    true
}

}