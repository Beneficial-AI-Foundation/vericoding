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
        invariant forall|j: int| 0 <= j < (i as int) ==> #[trigger] v@[j] >= 0
    {
        if v[i] < 0i {
            return false;
        }
        assert(forall|j: int| 0 <= j < (i as int)+1 ==> v@[j] >= 0);
    }
    return true;
}
// </vc-code>

fn main() {
}

}