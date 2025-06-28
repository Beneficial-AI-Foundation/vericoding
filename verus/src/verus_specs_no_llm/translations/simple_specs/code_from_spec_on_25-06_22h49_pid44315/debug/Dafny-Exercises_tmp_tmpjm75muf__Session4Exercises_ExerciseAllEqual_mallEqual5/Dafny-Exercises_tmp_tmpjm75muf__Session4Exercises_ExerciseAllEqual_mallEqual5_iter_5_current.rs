use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn allEqual(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s.spec_index(i) == s.spec_index(j)
}

fn allEqual5(v: Vec<int>) -> (b: bool)
    ensures
        b == allEqual(v@)
{
    if v.len() == 0 {
        assert(allEqual(v@)) by {
            assert(forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> v@.spec_index(i) == v@.spec_index(j)) by {
                // vacuously true since v@.len() == 0
            };
        };
        return true;
    }
    
    let first = v[0];
    let mut i = 1;
    
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            forall|k: int| 0 <= k < i ==> v@.spec_index(k) == first,
    {
        if v[i] != first {
            assert(!allEqual(v@)) by {
                assert(v@.spec_index(0) == first);
                assert(v@.spec_index(i as int) != first);
                assert(0 <= 0 < v@.len());
                assert(0 <= i < v@.len());
                assert(v@.spec_index(0) != v@.spec_index(i as int));
                // This directly contradicts the definition of allEqual
            };
            return false;
        }
        i += 1;
    }
    
    assert(allEqual(v@)) by {
        assert(i == v.len());
        assert(forall|k: int| 0 <= k < v@.len() ==> v@.spec_index(k) == first) by {
            // From the loop invariant, we know this holds for all k < i
            // And since i == v.len(), it holds for all valid indices
        };
        assert(forall|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() ==> 
               v@.spec_index(x) == v@.spec_index(y)) by {
            // Since all elements equal first, transitivity gives us equality between any two elements
            assert(forall|k: int| 0 <= k < v@.len() ==> v@.spec_index(k) == first);
        };
    };
    
    true
}

}