// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): not needed, the fix is in the code body */
// </vc-helpers>

// <vc-spec>
fn linear_search3(a: &Vec<i32>, p: spec_fn(i32) -> bool) -> (result: usize)
    requires 
        exists|i: int| 0 <= i < a.len() && p(a[i]),
    ensures 
        result < a.len(),
        p(a[result as int]),
        forall|k: int| 0 <= k < result ==> !p(a[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): use 'let tracked' to call spec fn from exec context via a proof block */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < (i as int) ==> !p(a[k]),
        decreases a.len() - i,
    {
        let current_val = a[i];
        let tracked found = proof { p(current_val) };
        if found {
            return i;
        }
        i = i + 1;
    }
    unreached()
}
// </vc-code>

}
fn main() {}