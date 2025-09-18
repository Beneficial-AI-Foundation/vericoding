// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type errors and improved element preservation proof */
proof fn delete_preserves_elements(arr: Vec<f32>, index: usize)
    requires
        arr.len() > 0,
        index < arr.len(),
    ensures
        forall|i: int| 0 <= i < arr.len() && i != index ==> 
            exists|j: int| 0 <= j < arr.len() - 1 && #[trigger] arr[i] == #[trigger] old(arr)[if j < index {j} else {j + 1}],
{
}

spec fn vec_to_seq(v: Vec<f32>) -> Seq<f32> {
    Seq::new(v.len() as nat, |i: int| v@[i])
}
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
/* code modified by LLM (iteration 5): Fixed type errors and improved loop invariant */
{
    let mut result = Vec::new();
    let len = arr.len();
    
    let mut i: usize = 0;
    while i < len 
        invariant 
            i <= len,
            result.len() == (if i <= index { i } else { i - 1 }) as usize,
            forall|j: int| 0 <= j < i && j < index ==> #[trigger] result[j] == arr[j],
            forall|j: int| index <= j < i - 1 ==> result[j] == arr[j + 1],
        decreases len - i
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