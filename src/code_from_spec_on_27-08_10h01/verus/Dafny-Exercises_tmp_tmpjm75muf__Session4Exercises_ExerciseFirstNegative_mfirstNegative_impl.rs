use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
proof fn lemma_positive_subrange_extends(s: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= s.len()
    requires positive(s.subrange(0, i))
    requires s[i] >= 0
    ensures positive(s.subrange(0, j))
{
}

proof fn lemma_positive_empty(s: Seq<int>)
    ensures positive(s.subrange(0, 0))
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn mfirstNegative(v: &[int]) -> (result: (bool, usize))
    ensures 
        (result.0 <==> exists|k: int| 0 <= k < v.len() && v[k] < 0) &&
        (result.0 ==> (result.1 < v.len() && v[result.1 as int] < 0 && positive(v@.subrange(0, result.1 as int))))
// </vc-spec>
// </vc-spec>

// <vc-code>
fn mfirstNegative(v: &[int]) -> (result: (bool, usize))
    ensures 
        (result.0 <==> exists|k: int| 0 <= k < v.len() && v[k] < 0) &&
        (result.0 ==> (result.1 < v.len() && v[result.1 as int] < 0 && positive(v@.subrange(0, result.1 as int))))
{
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            positive(v@.subrange(0, i as int)),
            forall|k: int| 0 <= k < i ==> v[k] >= 0
        decreases v.len() - i
    {
        if v[i] < 0 {
            return (true, i);
        }
        i += 1;
    }
    
    (false, 0)
}
// </vc-code>

fn main() {
}

}