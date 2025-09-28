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
    let mut b = true;
    let mut exec_i: usize = 0;
    let mut spec_i: int = 0;
    while exec_i < v.len()
        invariant
            spec_i == exec_i as int,
            0 <= spec_i <= v@.len(),
            b <==> forall|k: int| 0 <= k < spec_i ==> #[trigger] v@[k] >= 0,
        decreases v@.len() - spec_i,
    {
        if v[exec_i] < 0 {
            proof { assert(v@[spec_i] < 0); }
            b = false;
            break;
        } else {
            exec_i = exec_i + 1;
            spec_i = spec_i + 1;
        }
    }
    if !b {
        proof { assert(exists|k: int| 0 <= k < v@.len() && #[trigger] v@[k] < 0); }
    }
    b
}
// </vc-code>

fn main() {
}

}