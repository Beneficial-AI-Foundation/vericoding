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
            assert(i < v@.subrange(0, v.len() as int).len());
            assert(v@.subrange(0, v.len() as int).spec_index(i as int) == v@.spec_index(i as int));
            assert(v@.subrange(0, v.len() as int).spec_index(i as int) < 0);
            assert(!positive(v@.subrange(0, v.len() as int)));
            return false;
        }
        i += 1;
    }
    
    // At this point, i == v.len() and we need to prove positive holds
    assert(i == v.len());
    
    // Prove that all elements in the subrange are non-negative
    assert(forall|u: int| 0 <= u < i ==> v@.spec_index(u) >= 0);
    assert(v@.subrange(0, v.len() as int).len() == v@.len());
    assert(v@.subrange(0, v.len() as int).len() == i);
    
    // Establish the equivalence between subrange and original sequence
    assert(forall|u: int| 0 <= u < v@.len() ==> 
           v@.subrange(0, v.len() as int).spec_index(u) == v@.spec_index(u));
    
    // Prove positive for the subrange
    assert(forall|u: int| 0 <= u < v@.subrange(0, v.len() as int).len() ==> 
           v@.subrange(0, v.len() as int).spec_index(u) >= 0);
    
    assert(positive(v@.subrange(0, v.len() as int)));
    
    true
}

}