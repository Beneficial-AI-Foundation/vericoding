use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s.spec_index(u) >= 0
}

fn mpositive(v: Vec<int>) -> (b: bool)
    ensures
        b == positive(v@)
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|u: int| 0 <= u < i ==> v@.spec_index(u) >= 0
    {
        if v[i] < 0 {
            assert(!positive(v@)) by {
                assert(v@.spec_index(i as int) < 0);
                assert(0 <= i < v@.len());
            }
            return false;
        }
        i += 1;
    }
    
    assert(positive(v@)) by {
        assert(i == v.len());
        assert(forall|u: int| 0 <= u < v@.len() ==> v@.spec_index(u) >= 0);
    }
    
    true
}

}