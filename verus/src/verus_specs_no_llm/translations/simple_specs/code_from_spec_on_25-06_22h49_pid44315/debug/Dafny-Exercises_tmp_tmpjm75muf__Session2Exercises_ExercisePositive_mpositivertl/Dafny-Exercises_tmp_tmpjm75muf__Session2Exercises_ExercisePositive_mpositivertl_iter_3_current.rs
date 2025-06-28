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
            return false;
        }
        i += 1;
    }
    
    // At this point, i == v.len() and the invariant tells us
    // forall|u: int| 0 <= u < v.len() ==> v.spec_index(u) >= 0
    // We need to prove this is equivalent to positive(v@.subrange(0, v.len() as int))
    assert(i == v.len());
    assert(forall|u: int| 0 <= u < v.len() ==> v.spec_index(u) >= 0);
    
    // The subrange from 0 to v.len() is the same as the original sequence
    assert(v@.subrange(0, v.len() as int) =~= v@);
    assert(positive(v@.subrange(0, v.len() as int)));
    
    true
}

}