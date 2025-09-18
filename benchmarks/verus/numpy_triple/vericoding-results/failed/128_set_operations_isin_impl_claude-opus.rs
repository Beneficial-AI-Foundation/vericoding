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
    /* code modified by LLM (iteration 5): Fixed inner loop invariant to properly track found status */
    let mut result = Vec::new();
    let mut i = 0;
    while i < element.len()
        invariant
            0 <= i <= element.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> 
                (result[k] == true <==> exists|j: int| 0 <= j < test_elements.len() && element[k] == test_elements[j])
        decreases element.len() - i
    {
        let mut found = false;
        let mut j = 0;
        while j < test_elements.len()
            invariant
                0 <= i < element.len(),
                0 <= j <= test_elements.len(),
                found <==> (exists|k: int| 0 <= k < j && element[i as int] == test_elements[k])
            decreases test_elements.len() - j
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