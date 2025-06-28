use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u: int| 0<=u<s.len() ==> s.spec_index(u)>=0
}

fn mpositive4(v: Vec<int>) -> (b: bool)
    ensures
        b==positive(v@)
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |u: int| 0<=u<(i as int) ==> v@.spec_index(u)>=0
    {
        if v[i] < 0 {
            assert(!positive(v@)) by {
                assert(v@.spec_index(i as int) < 0);
                assert(0 <= (i as int) < v@.len());
                assert(exists |u: int| 0<=u<v@.len() && v@.spec_index(u)<0);
            }
            return false;
        }
        i += 1;
    }
    
    assert(positive(v@)) by {
        assert(i == v.len());
        assert(forall |u: int| 0<=u<(i as int) ==> v@.spec_index(u)>=0);
        assert((i as int) == v@.len());
    }
    
    true
}

}