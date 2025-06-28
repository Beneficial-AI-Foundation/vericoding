// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn allEqual(s: Seq<int>) -> bool {
    forall i,j::0<=i<s.len() && 0<=j<s.len() ==> s.spec_index(i)==s.spec_index(j)
}

fn mallEqual4(v: Vec<int>) -> (b: bool)
    ensures
        b==allEqual(v@.spec_index(0..v.len() as int))
{
    if v.len() == 0 {
        return true;
    }
    
    let first = v[0];
    for i in 1..v.len()
        invariant
            forall j: int :: 0 <= j < i ==> v@.spec_index(j) == first,
            0 <= i <= v.len(),
    {
        if v[i] != first {
            assert(!allEqual(v@.spec_index(0..v.len() as int))) by {
                assert(v@.spec_index(0) == first);
                assert(v@.spec_index(i as int) != first);
                assert(0 <= 0 < v.len());
                assert(0 <= i < v.len());
            }
            return false;
        }
        assert(v@.spec_index(i as int) == first);
    }
    
    assert(forall j: int :: 0 <= j < v.len() ==> v@.spec_index(j) == first) by {
        assert(forall j: int :: 0 <= j < v.len() ==> v@.spec_index(j) == first);
    }
    
    assert(allEqual(v@.spec_index(0..v.len() as int))) by {
        assert(forall i: int, j: int :: 0 <= i < v.len() && 0 <= j < v.len() ==> 
               v@.spec_index(i) == first && v@.spec_index(j) == first);
        assert(forall i: int, j: int :: 0 <= i < v.len() && 0 <= j < v.len() ==> 
               v@.spec_index(i) == v@.spec_index(j));
    }
    
    return true;
}

}