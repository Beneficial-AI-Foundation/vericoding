// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove unused helper function */
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
    /* code modified by LLM (iteration 5): fix ghost type usage in executable code */
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> !p(a[k]),
        decreases a.len() - i
    {
        if p(a[i]) {
            return i;
        }
        i += 1;
    }
    proof {
        assert(false);
    }
    0
}
// </vc-code>

}
fn main() {}