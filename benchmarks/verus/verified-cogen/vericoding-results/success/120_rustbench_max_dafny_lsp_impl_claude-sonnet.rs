// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn max_index_correct(a: &[i32], max_idx: usize) -> bool {
    0 <= max_idx < a.len() &&
    forall|k: int| 0 <= k < a.len() ==> a[k] <= a[max_idx as int]
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    requires
        a.len() > 0,
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut max_idx = 0;
    let mut i = 1;
    
    while i < a.len()
        invariant
            0 <= max_idx < a.len(),
            1 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] <= a[max_idx as int],
        decreases a.len() - i
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i += 1;
    }
    
    max_idx
}
// </vc-code>

}
fn main() {}