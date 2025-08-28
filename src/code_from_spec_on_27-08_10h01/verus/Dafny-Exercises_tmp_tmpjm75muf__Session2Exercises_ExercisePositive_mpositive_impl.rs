use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn mpositive(v: &[int]) -> (b: bool)
    ensures b == positive(v@)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    for i in 0..v.len()
        invariant forall|u: int| 0 <= u < i ==> v@[u] >= 0
    {
        if v[i] < 0 {
            return false;
        }
    }
    true
}
// </vc-code>

fn main() {
}

}