// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper modifications needed for this turn. */

// </vc-helpers>

// <vc-spec>
fn ndenumerate(arr: Vec<f32>) -> (result: Vec<(usize, f32)>)
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i as int].0 == i && result[i as int].1 == arr[i as int]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Adding decreases clause to the loop. */
{
    let mut result: Vec<(usize, f32)> = Vec::new();
    let mut i = 0;

    while i < arr.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j as int].0 == j && result[j as int].1 == arr[j as int],
        decreases arr.len() - i
    {
        result.push((i, arr[i]));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}