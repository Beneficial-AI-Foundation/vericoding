use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn mpositive(v: &[int]) -> (b: bool)
    ensures b == positive(v@)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> v@[j] >= 0,
    {
        if v[i] < 0 {
            assert(v@[i as int] < 0);
            assert(!positive(v@));
            return false;
        }
        i = i + 1;
    }
    assert(i == v.len());
    assert(forall|j: int| 0 <= j < v.len() ==> v@[j] >= 0);
    assert(positive(v@));
    true
}
// </vc-code>

fn main() {
}

}