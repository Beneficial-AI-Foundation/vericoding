use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s.spec_index(u) >= 0
}

fn mfirstNegative2(v: Vec<int>) -> (b: bool, i: int)
    ensures
        b <==> exists|k: int| 0 <= k < v@.len() && v@.spec_index(k) < 0,
        b ==> 0 <= i < v@.len() && v@.spec_index(i) < 0 && positive(v@.subrange(0, i as nat))
{
    let mut idx = 0;
    
    while idx < v.len()
        invariant
            0 <= idx <= v.len(),
            forall|k: int| 0 <= k < idx ==> v@.spec_index(k) >= 0
    {
        if v[idx] < 0 {
            assert(positive(v@.subrange(0, idx as nat))) by {
                let sub = v@.subrange(0, idx as nat);
                assert(sub.len() == idx);
                assert(forall|u: int| 0 <= u < sub.len() ==> {
                    &&& u < idx
                    &&& sub.spec_index(u) == v@.spec_index(u)
                    &&& v@.spec_index(u) >= 0
                });
            };
            return (true, idx as int);
        }
        idx += 1;
    }
    
    assert(!(exists|k: int| 0 <= k < v@.len() && v@.spec_index(k) < 0)) by {
        assert(idx == v.len());
        assert(forall|k: int| 0 <= k < v@.len() ==> v@.spec_index(k) >= 0);
    };
    
    return (false, 0);
}

}