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
                assert(0 <= i < v.len());
                assert(v@.spec_index(i as int) == v[i]);
                assert(v[i] != first);
                assert(v@.spec_index(i as int) != first);
                assert(0 <= 0 < v@.len());
                assert(0 <= i as int < v@.len());
                assert(v@.spec_index(0) != v@.spec_index(i as int));
                // Show that allEqual is false by showing the negation of the forall
                assert(!(forall|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() ==> 
                        v@.spec_index(x) == v@.spec_index(y))) by {
                    // We have a counterexample: x=0, y=i
                    assert(0 <= 0 < v@.len() && 0 <= i as int < v@.len());
                    assert(v@.spec_index(0) != v@.spec_index(i as int));
                };
            };
            return false;
        }
        assert(v@.spec_index(i as int) == first);
        i += 1;
    }
    
    assert(allEqual(v@)) by {
        assert(i == v.len());
        assert(forall|k: int| 0 <= k < v@.len() ==> v@.spec_index(k) == first) by {
            // This follows from the loop invariant when i == v.len()
            assert(forall|k: int| 0 <= k < i ==> v@.spec_index(k) == first);
            assert(i == v.len());
            assert(i as int == v@.len());
        };
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

The key fixes I made:


The main issue was that Verus needs explicit bounds checking when converting between `usize` and `int`, and the verifier needed help understanding that the loop invariant maintained the property for all elements up to the current index.