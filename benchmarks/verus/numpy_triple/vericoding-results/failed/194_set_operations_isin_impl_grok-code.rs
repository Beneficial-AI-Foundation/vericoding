// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed executable indexing and length to use Vec access instead of ghost sequence */
fn contains(test_elements: &Vec<f32>, elem: f32) -> (found: bool)
    ensures found <==> exists|i: int| 0 <= i < test_elements@.len() && test_elements@[i] == elem
{
    let mut i: usize = 0;
    while i < test_elements.len()
        invariant
            0 <= i <= test_elements.len(),
            forall|j: int| 0 <= j < (i as int) ==> test_elements@[j] != elem
        decreases test_elements.len() - i
    {
        if test_elements[i] == elem {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn numpy_isin(element: Vec<f32>, test_elements: Vec<f32>) -> (result: Vec<bool>)
    ensures 
        result.len() == element.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == true <==> exists|j: int| 0 <= j < test_elements.len() && element[i] == test_elements[j])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed executable indexing and length to use Vec access instead of ghost sequence */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < element.len()
        invariant
            0 <= i <= element.len(),
            result@.len() == (i as int),
            forall|j: int| 0 <= j < (i as int) ==> 
                (result@[j] == true <==> exists|k: int| 0 <= k < test_elements@.len() && element@[j] == test_elements@[k])
        decreases element.len() - i
    {
        let res_i = contains(&test_elements, element[i]);
        result.push(res_i);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}