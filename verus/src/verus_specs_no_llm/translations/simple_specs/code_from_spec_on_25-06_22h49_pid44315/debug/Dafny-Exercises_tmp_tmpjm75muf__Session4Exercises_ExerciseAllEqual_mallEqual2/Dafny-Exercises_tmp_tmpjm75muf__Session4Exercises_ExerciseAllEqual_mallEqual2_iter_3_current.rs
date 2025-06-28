use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn allEqual(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
}

fn allEqual2(v: Vec<int>) -> (b: bool)
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
            v.len() > 0,
            first == v[0],
            forall|k: int| 0 <= k < i ==> v[k] == first,
    {
        if v[i] != first {
            // Prove that returning false is correct
            assert(v[0] != v[i as int]);
            assert(exists|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() && v@[x] != v@[y]) by {
                assert(v@[0] != v@[i as int]);
            }
            assert(!allEqual(v@));
            return false;
        }
        i = i + 1;
    }
    
    // Prove that all elements are equal to first
    assert(forall|k: int| 0 <= k < v.len() ==> v[k] == first);
    
    // Prove this implies allEqual
    assert(forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> {
        v@[i] == first && v@[j] == first
    }) by {
        assert(forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> v@[i] == v@[j]);
    }
    
    assert(allEqual(v@));
    return true;
}

}