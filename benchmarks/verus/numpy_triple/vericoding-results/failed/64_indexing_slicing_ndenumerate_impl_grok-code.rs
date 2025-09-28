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
        forall|i: int| 0 <= i < result.len() ==> result[i as int].0 == i && result[i as int].1 == arr[i as int]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed indexing in invariant to use sequence view with @ and adjusted types to int for consistency */{
    let mut result: Vec<(usize, f32)> = Vec::with_capacity(arr.len());
    let mut i: int = 0;
    while i < arr@.len()
        invariant
            0 <= i <= arr@.len(),
            result@.len() == i,
            forall |j: int| 0 <= j < i ==> #[trigger] result@[j].0 == j && #[trigger] result@[j].1 == arr@[j],
        decreases arr@.len() - i
    {
        result.push((i as usize, arr[i as usize]));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}