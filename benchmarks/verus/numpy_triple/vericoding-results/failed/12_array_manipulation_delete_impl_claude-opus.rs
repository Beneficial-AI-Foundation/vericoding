// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed postcondition verification by ensuring all elements except at index are preserved */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == if i <= index { i } else { (i - 1) as usize },
            forall|j: int| 0 <= j < i && j < index ==> #[trigger] result[j] == arr[j],
            forall|j: int| index < j && j < i ==> result[j - 1] == #[trigger] arr[j],
            forall|k: int| 0 <= k < i && k != index ==> 
                exists|m: int| 0 <= m < result.len() && result[m] == arr[k],
        decreases arr.len() - i
    {
        if i != index {
            result.push(arr[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}