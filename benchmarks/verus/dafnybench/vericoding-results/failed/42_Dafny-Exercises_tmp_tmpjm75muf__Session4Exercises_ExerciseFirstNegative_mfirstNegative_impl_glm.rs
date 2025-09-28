use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
proof fn lemma_extend_positive(v: &[int], i: usize)
    requires
        0 <= i < v.len(),
        forall|j: int| 0 <= j < i as int ==> v@[j] >= 0,
        v[i] >= 0
    ensures
        forall|j: int| 0 <= j < (i+1) as int ==> #[trigger] v@[j] >= 0;
{
    assert(forall|j: int| 0 <= j < i as int ==> v@[j] >= 0);
    assert(v@[i as int] == v[i]);
    assert(v[i] >= 0);
    forall|j: int| 0 <= j < (i+1) as int
        ensures #[trigger] v@[j] >= 0
    {
        if j < i as int {
            assert(v@[j] >= 0);
        } else {
            assert(j == i as int);
            assert(v@[j] == v[i]);
        }
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
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i as int ==> #[trigger] v@[j] >= 0
    {
        if v[i] < 0 {
            return (true, i);
        } else {
            proof {
                lemma_extend_positive(v, i);
            }
            i += 1;
        }
    }
    (false, 0)
}
// </vc-code>

fn main() {
}

}