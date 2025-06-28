use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn allEqual(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
}

fn allEqual1(v: Vec<int>) -> (b: bool)
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
            forall|k: int| 0 <= k < i ==> v@[k] == first,
    {
        if v[i] != first {
            assert(!allEqual(v@)) by {
                // We have a counterexample: position 0 and position i
                assert(v@[0] == first);
                assert(v@[i as int] != first);
                assert(0 <= 0 < v@.len() && 0 <= (i as int) < v@.len());
                assert(v@[0] != v@[i as int]);
                // This directly contradicts the definition of allEqual
            };
            return false;
        }
        i += 1;
    }
    
    // After the loop, we know all elements equal first
    assert(forall|k: int| 0 <= k < v@.len() ==> v@[k] == first);
    
    // Prove allEqual(v@) holds
    assert(allEqual(v@)) by {
        assert forall|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() implies v@[x] == v@[y] by {
            assert(v@[x] == first);
            assert(v@[y] == first);
        }
    };
    
    true
}

}