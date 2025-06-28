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
            assert(forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> 
                   v@.spec_index(i) == v@.spec_index(j)) by {
                assert(v@.len() == 0);
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
                assert(v@.spec_index(i as int) == v[i]);
                assert(v[i] != first);
                assert(v@.spec_index(i as int) != first);
                assert(0 <= 0 < v@.len());
                assert(0 <= i < v@.len());
                assert(v@.spec_index(0) != v@.spec_index(i as int));
                assert(exists|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() && 
                       v@.spec_index(x) != v@.spec_index(y));
            };
            return false;
        }
        assert(v@.spec_index(i as int) == first);
        i += 1;
    }
    
    assert(allEqual(v@)) by {
        assert(i == v.len());
        assert(forall|k: int| 0 <= k < v@.len() ==> v@.spec_index(k) == first);
        assert(forall|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() ==> 
               v@.spec_index(x) == v@.spec_index(y)) by {
            forall|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() 
            implies v@.spec_index(x) == v@.spec_index(y) by {
                assert(v@.spec_index(x) == first);
                assert(v@.spec_index(y) == first);
            }
        };
    };
    
    true
}

}