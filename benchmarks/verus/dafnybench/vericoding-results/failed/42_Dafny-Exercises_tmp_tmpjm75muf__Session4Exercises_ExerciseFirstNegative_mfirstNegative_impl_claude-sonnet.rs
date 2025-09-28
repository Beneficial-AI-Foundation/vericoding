use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
spec fn lemma_positive_subrange_extends(s: Seq<int>, i: int, j: int) -> bool
    recommends 
        0 <= i <= j <= s.len(),
        positive(s.subrange(0, i))
{
    positive(s.subrange(0, j)) <==> (positive(s.subrange(0, i)) && forall|k: int| i <= k < j ==> s[k] >= 0)
}

proof fn lemma_positive_empty(s: Seq<int>)
    ensures positive(s.subrange(0, 0))
{
    assert(s.subrange(0, 0).len() == 0);
    assert(forall|u: int| 0 <= u < 0 ==> s.subrange(0, 0)[u] >= 0) by {
        assert(forall|u: int| !(0 <= u < 0)) by {}
    }
}
// </vc-helpers>

// <vc-spec>
fn mfirstNegative(v: &[int]) -> (result: (bool, usize))
    ensures 
        (result.0 <==> exists|k: int| 0 <= k < v.len() && v[k] < 0) &&
        (result.0 ==> (result.1 < v.len() && v[result.1 as int] < 0 && positive(v@.subrange(0, result.1 as int))))
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    
    proof {
        lemma_positive_empty(v@);
    }
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            positive(v@.subrange(0, i as int)),
            forall|k: int| 0 <= k < i ==> v[k] >= 0
    {
        if v[i] < 0 {
            return (true, i);
        }
        
        assert(v[i as int] >= 0);
        assert(forall|k: int| 0 <= k < i + 1 ==> v[k] >= 0) by {
            assert(forall|k: int| 0 <= k < i ==> v[k] >= 0);
            assert(v[i as int] >= 0);
        }
        
        i += 1;
        
        assert(positive(v@.subrange(0, i as int))) by {
            assert(forall|k: int| 0 <= k < i ==> v[k] >= 0);
            assert(forall|u: int| 0 <= u < v@.subrange(0, i as int).len() ==> v@.subrange(0, i as int)[u] >= 0) by {
                assert(v@.subrange(0, i as int).len() == i);
                assert(forall|u: int| 0 <= u < i ==> v@.subrange(0, i as int)[u] == v[u]);
            }
        }
    }
    
    assert(i == v.len());
    assert(forall|k: int| 0 <= k < v.len() ==> v[k] >= 0);
    assert(!(exists|k: int| 0 <= k < v.len() && v[k] < 0)) by {
        if exists|k: int| 0 <= k < v.len() && v[k] < 0 {
            let witness_k = choose|k: int| 0 <= k < v.len() && v[k] < 0;
            assert(v[witness_k] >= 0);
            assert(false);
        }
    }
    
    (false, 0)
}
// </vc-code>

fn main() {
}

}