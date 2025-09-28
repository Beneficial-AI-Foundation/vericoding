use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mpositive(v: &[int]) -> (b: bool)
    ensures b == positive(v@)
// </vc-spec>
// <vc-code>
{
    for i in 0..v.len()
        invariant
            forall|u: int| 0 <= u < i ==> v@[u] >= 0
    {
        if v[i] < 0 {
            assert(v@[i as int] < 0);
            assert(0 <= i < v@.len());
            return false;
        }
    }
    assert(forall|u: int| 0 <= u < v@.len() ==> v@[u] >= 0);
    true
}
// </vc-code>

fn main() {
}

}