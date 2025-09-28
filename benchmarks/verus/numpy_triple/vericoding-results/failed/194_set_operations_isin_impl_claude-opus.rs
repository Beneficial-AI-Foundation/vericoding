// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_isin(element: Vec<f32>, test_elements: Vec<f32>) -> (result: Vec<bool>)
    ensures 
        result.len() == element.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == true <==> exists|j: int| 0 <= j < test_elements.len() && element[i] == test_elements[j])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatch by converting usize to int in specifications */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < element.len()
        invariant
            i <= element.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> 
                (result[k] == true <==> exists|j: int| 0 <= j < test_elements.len() as int && element[k] == test_elements[j])
    {
        let mut found = false;
        let mut j: usize = 0;
        while j < test_elements.len()
            invariant
                j <= test_elements.len(),
                found <==> exists|k: int| 0 <= k < j as int && element[i as int] == test_elements[k]
        {
            if element[i] == test_elements[j] {
                found = true;
            }
            j = j + 1;
        }
        result.push(found);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}