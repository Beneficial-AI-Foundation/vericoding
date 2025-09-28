// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): minimal helper to keep section valid */
proof fn helper_noop() { }

// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct Vec by iterating over the Seq and pushing elements */
    let n: int = xs.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == xs[j],
        decreases n - i
    {
        result.push(xs[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}