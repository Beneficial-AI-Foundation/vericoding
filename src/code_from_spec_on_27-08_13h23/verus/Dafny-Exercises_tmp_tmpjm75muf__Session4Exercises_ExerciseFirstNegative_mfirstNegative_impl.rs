use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
proof fn lemma_subrange_positive(v: Seq<int>, end: int)
    requires
        0 <= end <= v.len(),
        positive(v.subrange(0, end)),
    ensures
        forall|i: int| 0 <= i < end ==> v[i] >= 0,
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
        (result.0 ==> (result.1 < v.len() && v[result.1 as int] < 0 && positive(v@.subrange(0, result.1 as int)))),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            positive(v@.subrange(0, i as int)),
    {
        if v[i] < 0 {
            return (true, i);
        }
        i = i + 1;
    }
    (false, 0)
}
// </vc-code>

fn main() {
}

}