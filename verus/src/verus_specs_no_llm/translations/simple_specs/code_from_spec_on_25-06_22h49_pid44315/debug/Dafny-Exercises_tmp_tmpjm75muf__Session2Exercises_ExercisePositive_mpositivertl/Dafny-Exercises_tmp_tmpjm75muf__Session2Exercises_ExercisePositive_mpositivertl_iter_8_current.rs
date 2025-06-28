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
            forall|u: int| 0 <= u < i ==> v@.spec_index(u) >= 0
    {
        if v[i] < 0 {
            // Prove that the postcondition holds when returning false
            assert(v[i] < 0);
            assert(v@.spec_index(i as int) < 0);
            // Show that subrange(0, v.len()) contains this negative element
            assert(0 <= i < v.len());
            assert(v@.subrange(0, v.len() as int) =~= v@);
            assert(v@.subrange(0, v.len() as int).spec_index(i as int) == v@.spec_index(i as int));
            assert(v@.subrange(0, v.len() as int).spec_index(i as int) < 0);
            assert(!positive(v@.subrange(0, v.len() as int)));
            return false;
        }
        i += 1;
    }
    
    // At this point, i == v.len() and we need to prove positive holds
    assert(i == v.len());
    
    // The key insight: subrange(0, v.len()) is equivalent to the full sequence
    assert(v@.subrange(0, v.len() as int) =~= v@);
    
    // From the loop invariant, we know all elements from 0 to i-1 are non-negative
    // Since i == v.len(), this means all elements in v@ are non-negative
    assert(forall|u: int| 0 <= u < v@.len() ==> v@.spec_index(u) >= 0);
    
    // Since subrange(0, v.len()) equals v@, positive holds for the subrange
    assert(positive(v@));
    assert(positive(v@.subrange(0, v.len() as int)));
    
    true
}

}