// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mlast_maximum(v: &[i32]) -> (i: usize)
    requires v.len() > 0
    ensures 
        i < v.len(),
        forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k],
        forall|l: int| i < l < v.len() ==> v[i as int] > v[l],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type errors in invariant indices */
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            0 <= max_idx < i,
            forall|k: int| 0 <= k < (i as int) ==> v[max_idx as int] >= v[k],
            forall|l: int| (max_idx as int) < l < (i as int) ==> v[max_idx as int] > v[l],
        decreases v.len() - i
    {
        if v[i] >= v[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    max_idx
}
// </vc-code>

}
fn main() {}