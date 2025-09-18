// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): usize to int conversion helper */ fn usize_to_int(a: usize) -> int { a as int }
// </vc-helpers>

// <vc-spec>
fn delete(arr: Vec<f32>, index: usize) -> (result: Vec<f32>)
    requires 
        arr.len() > 0,
        index < arr.len(),
    ensures 
        result.len() == arr.len() - 1,
        forall|i: int| 0 <= i < index ==> #[trigger] result[i] == arr[i],
        forall|i: int| index <= i < result.len() ==> result[i] == #[trigger] arr[i + 1],
        forall|i: int| 0 <= i < arr.len() && i != index ==> 
            exists|j: int| 0 <= j < result.len() && #[trigger] result[j] == #[trigger] arr[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build resulting vec skipping index using usize counters and proper invariants */
    let mut res: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < index
        invariant i <= index;
        invariant res.len() == i;
        invariant forall|t: int| 0 <= t && t < usize_to_int(i) ==> res@[t] == arr@[t];
    {
        res.push(arr[i]);
        i += 1;
    }

    let mut j: usize = index + 1;
    while j < arr.len()
        invariant index + 1 <= j && j <= arr.len();
        invariant res.len() == j - 1;
        invariant forall|t: int| 0 <= t && t < usize_to_int(index) ==> res@[t] == arr@[t];
        invariant forall|t: int| usize_to_int(index) <= t && t < usize_to_int(res.len()) ==> res@[t] == arr@[t + 1];
    {
        res.push(arr[j]);
        j += 1;
    }

    res
}
// </vc-code>

}
fn main() {}