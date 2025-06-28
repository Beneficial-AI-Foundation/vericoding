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
        assert(allEqual(v@)) by {
            assert(forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> 
                v@.spec_index(i) == v@.spec_index(j)) by {
                // vacuously true since v@.len() == 0
            }
        };
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
            assert(v@.spec_index(0) == first);
            assert(v@.spec_index(i as int) != first);
            assert(0 <= 0 < v@.len() && 0 <= i < v@.len());
            assert(v@.spec_index(0) != v@.spec_index(i as int));
            
            // Prove allEqual is false by showing the definition is violated
            assert(!allEqual(v@)) by {
                // We have a counterexample: indices 0 and i have different values
                assert(0 <= 0 < v@.len() && 0 <= i < v@.len());
                assert(v@.spec_index(0) != v@.spec_index(i as int));
                // This contradicts the definition of allEqual
                assert(!(forall|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() ==> 
                    v@.spec_index(x) == v@.spec_index(y)));
            };
            return false;
        }
        i += 1;
    }
    
    // When we exit the loop, i == v.len()
    assert(i == v.len());
    assert(forall|k: int| 0 <= k < v.len() ==> v@.spec_index(k) == first);
    
    // Now prove allEqual holds
    assert(allEqual(v@)) by {
        assert(forall|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() ==> {
            &&& v@.spec_index(x) == first
            &&& v@.spec_index(y) == first
            &&& v@.spec_index(x) == v@.spec_index(y)
        });
    };
    
    true
}

}