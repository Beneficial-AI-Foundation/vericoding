use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
spec fn positive_subrange_len(s: Seq<int>, start: int, end: int) -> bool 
    recommends 0 <= start <= end <= s.len()
{
    forall|u: int| start <= u < end ==> s[u] >= 0
}

proof fn lemma_positive_empty(s: Seq<int>)
    ensures
        positive_subrange_len(s, 0, 0)
{
    assert(forall|u: int| 0 <= u < 0 ==> s[u] >= 0);
}

proof fn lemma_positive_extend(s: Seq<int>, i: int)
    requires
        0 <= i < s.len(),
        positive_subrange_len(s, 0, i),
        s[i] >= 0
    ensures
        positive_subrange_len(s, 0, i + 1)
{
    assert forall|u: int| 0 <= u < i+1 implies s[u] >= 0 by {
        if u < i {
            assert(s[u] >= 0);
        } else {
            assert(u == i);
            assert(s[i] >= 0);
        }
    };
}

proof fn lemma_negative_found(s: Seq<int>, i
// </vc-helpers>

// <vc-spec>
fn mfirstNegative(v: &[int]) -> (result: (bool, usize))
    ensures 
        (result.0 <==> exists|k: int| 0 <= k < v.len() && v[k] < 0) &&
        (result.0 ==> (result.1 < v.len() && v[result.1 as int] < 0 && positive(v@.subrange(0, result.1 as int))))
// </vc-spec>
// <vc-code>
spec fn positive_subrange_len(s: Seq<int>, start: int, end: int) -> bool 
    recommends 0 <= start <= end <= s.len()
{
    forall|u: int| start <= u < end ==> s[u] >= 0
}

proof fn lemma_positive_empty(s: Seq<int>)
    ensures
        positive_subrange_len(s, 0, 0)
{
    assert(forall|u: int| 0 <= u < 0 ==> s[u] >= 0);
}

proof fn lemma_positive_extend(s: Seq<int>, i: int)
    requires
        0 <= i < s.len(),
        positive_subrange_len(s, 0, i),
        s[i] >= 0
    ensures
        positive_subrange_len(s, 0, i + 1)
{
    assert forall|u: int| 0 <= u < i+1 implies s[u] >= 0 by {
        if u < i {
            assert(s[u] >= 0);
        } else {
            assert(u == i);
            assert(s[i] >= 0);
        }
    };
}

proof fn lemma_negative_found(s: Seq<int>, i
// </vc-code>

fn main() {
}

}