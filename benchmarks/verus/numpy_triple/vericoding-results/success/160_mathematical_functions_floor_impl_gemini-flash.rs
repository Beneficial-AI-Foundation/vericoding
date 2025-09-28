// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed content as no helpers are needed. */
// </vc-helpers>

// <vc-spec>
fn numpy_floor(x: Vec<i32>) -> (result: Vec<i32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x[i],
        forall|i: int| 0 <= i < result.len() ==> x[i] < result[i] + 1,
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && x[i] <= x[j] ==> result[i] <= result[j],
        forall|i: int| 0 <= i < result.len() ==> result[i] == x[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed type mismatches (int vs usize) and indexing issues. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < x.len()
        invariant
            0 <= i as int,
            i as int <= x.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == x[j],
        decreases x.len() - i
    {
        result.push(x[i] as i32);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}