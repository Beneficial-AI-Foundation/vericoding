// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple max for i32 */
fn max_i32(a: i32, b: i32) -> i32 { if a >= b { a } else { b } }
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
    /* code modified by LLM (iteration 2): fix index types in invariants and implement max loop */
    let mut idx: usize = 0;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            idx < a.len(),
            i <= a.len(),
            forall|k: int| 0 <= k && k < (i as int) ==> a[k] <= a[idx as int],
        decreases a.len() - i
    {
        if a[i] > a[idx] {
            idx = i;
        }
        i = i + 1;
    }
    idx
}
// </vc-code>

}
fn main() {}