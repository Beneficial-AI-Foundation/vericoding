use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn mfirstNegative(v: &[int]) -> (result: (bool, usize))
    ensures 
        (result.0 <==> exists|k: int| 0 <= k < v.len() && v[k] < 0) &&
        (result.0 ==> (result.1 < v.len() && v[result.1 as int] < 0 && positive(v@.subrange(0, result.1 as int))))
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            positive(v@.subrange(0, i as int)),
            forall|k: int| 0 <= k < i ==> v@[k] >= 0,
    {
        if v[i] < 0 {
            assert(v@[i as int] < 0);
            assert(positive(v@.subrange(0, i as int)));
            return (true, i);
        }
        i = i + 1;
    }
    
    assert(i == v.len());
    assert(forall|k: int| 0 <= k < v.len() ==> v@[k] >= 0);
    (false, 0)
}
// </vc-code>

fn main() {
}

}