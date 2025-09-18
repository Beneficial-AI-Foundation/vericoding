// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ndenumerate(arr: Vec<f32>) -> (result: Vec<(usize, f32)>)
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].0 == i && result[i].1 == arr[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed indexing in invariant and added trigger */
    let mut result: Vec<(usize, f32)> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j].0 == j && result@[j].1 == arr@[j],
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