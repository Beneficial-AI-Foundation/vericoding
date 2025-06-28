use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s.spec_index(u) >= 0
}

fn mpositivertl(v: Vec<int>) -> (b: bool)
    ensures
        b == positive(v@.subrange(0, v.len() as int))
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|u: int| 0 <= u < i ==> v.spec_index(u) >= 0
    {
        if v[i] < 0 {
            // Prove that the postcondition holds when returning false
            assert(v[i] < 0);
            assert(i < v.len());
            assert(v@.spec_index(i) < 0);
            assert(v@.subrange(0, v.len() as int).spec_index(i) < 0);
            assert(!positive(v@.subrange(0, v.len() as int)));
            return false;
        }
        i += 1;
    }
    
    // At this point, i == v.len() and we need to prove positive holds
    assert(i == v.len());
    
    // Prove that v@.subrange(0, v.len() as int) equals v@
    assert(v@.subrange(0, v.len() as int) =~= v@) by {
        assert(v@.len() == v.len());
        assert(forall|j: int| 0 <= j < v@.len() ==> 
            v@.subrange(0, v.len() as int).spec_index(j) == v@.spec_index(j));
    }
    
    // Use the loop invariant to prove positive
    assert(forall|u: int| 0 <= u < v.len() ==> v.spec_index(u) >= 0);
    assert(forall|u: int| 0 <= u < v@.len() ==> v@.spec_index(u) >= 0);
    assert(forall|u: int| 0 <= u < v@.subrange(0, v.len() as int).len() ==> 
           v@.subrange(0, v.len() as int).spec_index(u) >= 0);
    assert(positive(v@.subrange(0, v.len() as int)));
    
    true
}

}