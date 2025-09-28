// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper functions are needed for this task. */
// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type errors for `i` and indexing into `xs`. Removed unnecessary cast to `nat`. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            0 <= i as nat,
            i as nat <= xs.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == xs[j],
        decreases (xs.len() as int) - (i as int)
    {
        result.push(xs.index(i as int));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}