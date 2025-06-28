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
            0 < i <= v.len(),
            v.len() > 0,
            first == v[0],
            forall|k: int| 0 <= k < i ==> v@[k] == first,
    {
        if v[i] != first {
            // Prove that returning false is correct
            assert(!allEqual(v@)) by {
                // We have a witness that not all elements are equal
                assert(v@[0] == first);
                assert(v@[i as int] != first);
                assert(v@[0] != v@[i as int]);
                assert(0 <= 0 < v@.len());
                assert(0 <= i as int < v@.len());
                // This contradicts allEqual directly
                assert(!(forall|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() ==> v@[x] == v@[y]));
            }
            return false;
        }
        i = i + 1;
    }
    
    // At this point, we know all elements are equal to first
    assert(i == v.len());
    assert(forall|k: int| 0 <= k < v@.len() ==> v@[k] == first);
    
    // Prove this implies allEqual
    assert(allEqual(v@)) by {
        assert(forall|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() ==> {
            v@[x] == v@[y]
        }) by {
            // For any two valid indices x and y
            assert(forall|x: int, y: int| 0 <= x < v@.len() && 0 <= y < v@.len() ==> {
                &&& v@[x] == first  // from our invariant
                &&& v@[y] == first  // from our invariant
                &&& v@[x] == v@[y]  // transitivity
            });
        }
    }
    
    return true;
}

}