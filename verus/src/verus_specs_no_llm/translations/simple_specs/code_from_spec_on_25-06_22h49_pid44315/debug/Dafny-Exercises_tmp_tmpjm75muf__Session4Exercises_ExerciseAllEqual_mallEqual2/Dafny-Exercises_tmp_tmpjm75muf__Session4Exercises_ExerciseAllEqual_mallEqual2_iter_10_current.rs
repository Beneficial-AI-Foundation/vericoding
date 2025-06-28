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
    let mut i: usize = 1;
    
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            v.len() > 0,
            first == v[0],
            forall|k: int| 0 <= k < i ==> v@[k] == first,
    {
        if v[i] != first {
            assert(!allEqual(v@)) by {
                assert(0 <= 0 < v@.len());
                assert(0 <= i < v@.len());
                assert(v@[0] == first);
                assert(v@[i as int] != first);
                assert(v@[0] != v@[i as int]);
            }
            return false;
        }
        i = i + 1;
    }
    
    // At this point, we know all elements are equal to first
    assert(forall|k: int| 0 <= k < v@.len() ==> v@[k] == first);
    
    // Prove this implies allEqual
    assert(allEqual(v@)) by {
        assert(forall|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() ==> {
            v@[x] == first && v@[y] == first
        });
        assert(forall|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() ==> v@[x] == v@[y]);
    }
    
    true
}

}