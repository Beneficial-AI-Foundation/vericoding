// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mpositive(v: &[int]) -> (b: bool)
    ensures b == positive(v@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by removing invalid 'int' suffix */
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|k: int| 0 <= k < i ==> v@[k] >= 0,
        decreases v.len() - i
    {
        if v[i] < 0 {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}