// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial proof helper */
proof fn helper_noop() {
}

// </vc-helpers>

// <vc-spec>
fn swap_first_and_last(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        result.len() == a.len(),
        result[0] == a[a.len() - 1],
        result[result.len() - 1] == a[0],
        forall|i: int| 1 <= i < result.len() - 1 ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): clone input vector and swap first and last elements without using Vec::swap to avoid complex &mut args */
    let n = a.len();
    let mut result = a.clone();
    if n > 1 {
        let last = n - 1;
        let tmp = result[0];
        result[0] = result[last];
        result[last] = tmp;
    }
    result
}
// </vc-code>

}
fn main() {}