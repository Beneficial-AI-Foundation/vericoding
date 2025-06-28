use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn allEqual(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
}

fn allEqual4(v: Vec<int>) -> (b: bool)
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
            forall|j: int| 0 <= j < i ==> v@[j] == first,
            1 <= i <= v.len(),
    {
        if v[i] != first {
            assert(!allEqual(v@)) by {
                assert(v@[0] == first);
                assert(v@[i as int] != first);
                assert(0 <= 0 < v@.len());
                assert(0 <= i < v@.len());
            };
            return false;
        }
        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j < v@.len() ==> v@[j] == first) by {
        assert(forall|j: int| 0 <= j < i ==> v@[j] == first);
        assert(i == v.len());
    };
    
    assert(allEqual(v@)) by {
        assert(forall|k1: int, k2: int| 0 <= k1 < v@.len() && 0 <= k2 < v@.len() ==> {
            &&& v@[k1] == first
            &&& v@[k2] == first
            &&& v@[k1] == v@[k2]
        });
    };
    
    true
}

}