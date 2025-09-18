// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper to prove element existence in result */
proof fn prove_element_exists(arr: Vec<f32>, result: Vec<f32>, index: usize, target_i: int)
    requires
        arr.len() > 0,
        index < arr.len(),
        result.len() == arr.len() - 1,
        0 <= target_i < arr.len(),
        target_i != index,
        forall|k: int| 0 <= k < index ==> result[k] == arr[k],
        forall|k: int| index <= k < result.len() ==> result[k] == arr[k + 1],
    ensures
        exists|j: int| 0 <= j < result.len() && result[j] == arr[target_i]
{
    if target_i < index {
        assert(result[target_i] == arr[target_i]);
    } else {
        let j = target_i - 1;
        assert(index <= j < result.len());
        assert(result[j] == arr[j + 1]);
        assert(j + 1 == target_i);
        assert(result[j] == arr[target_i]);
    }
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
{
    /* code modified by LLM (iteration 5): fixed trigger inference by providing explicit witness in forall */
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == if i <= index { i } else { (i - 1) as usize },
            forall|k: int| 0 <= k < result.len() && k < index ==> result[k] == arr[k],
            forall|k: int| 0 <= k < result.len() && k >= index ==> result[k] == arr[k + 1],
        decreases arr.len() - i
    {
        if i != index {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    proof {
        assert forall|target_i: int| 0 <= target_i < arr.len() && target_i != index implies
            #[trigger] exists|j: int| 0 <= j < result.len() && result[j] == arr[target_i]
        by {
            prove_element_exists(arr, result, index, target_i);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}