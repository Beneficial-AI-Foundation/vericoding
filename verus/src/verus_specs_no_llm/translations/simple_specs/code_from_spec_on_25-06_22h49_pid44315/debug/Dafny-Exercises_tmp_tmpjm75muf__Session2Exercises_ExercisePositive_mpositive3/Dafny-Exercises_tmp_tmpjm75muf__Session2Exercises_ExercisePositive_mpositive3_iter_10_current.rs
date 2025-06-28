use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u: int| 0<=u<s.len() ==> s.spec_index(u)>=0
}

fn mpositive3(v: Vec<int>) -> (b: bool)
    ensures
        b == positive(v@.subrange(0, v.len() as int))
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |u: int| 0 <= u < i ==> v@.spec_index(u) >= 0,
    {
        if v[i] < 0 {
            proof {
                let seq = v@.subrange(0, v.len() as int);
                assert(seq.len() == v@.len());
                assert(forall |k: int| 0 <= k < seq.len() ==> seq.spec_index(k) == v@.spec_index(k));
                assert(0 <= i < v.len());
                assert(i < seq.len());
                assert(seq.spec_index(i as int) == v@.spec_index(i as int));
                assert(v@.spec_index(i as int) == v[i]);
                assert(v[i] < 0);
                assert(seq.spec_index(i as int) < 0);
                // Since we found an element < 0, positive is false
                assert(!positive(seq));
            }
            return false;
        }
        i += 1;
    }
    
    proof {
        let seq = v@.subrange(0, v.len() as int);
        assert(seq.len() == v@.len());
        assert(forall |k: int| 0 <= k < seq.len() ==> seq.spec_index(k) == v@.spec_index(k));
        assert(i == v.len());
        assert(forall |u: int| 0 <= u < i ==> v@.spec_index(u) >= 0);
        // Since i == v.len(), we have checked all elements
        assert(forall |u: int| 0 <= u < v@.len() ==> v@.spec_index(u) >= 0);
        // This translates to the subsequence property
        assert(forall |u: int| 0 <= u < seq.len() ==> seq.spec_index(u) >= 0);
        assert(positive(seq));
    }
    return true;
}

}