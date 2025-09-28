// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed invariant to allow element to be found in current iteration */
fn contains_element(element: f32, test_elements: &Vec<f32>) -> (result: bool)
    ensures
        result == true <==> exists|j: int| 0 <= j < test_elements.len() && element == test_elements[j]
{
    let mut i = 0;
    while i < test_elements.len()
        invariant
            0 <= i <= test_elements.len(),
            forall|k: int| 0 <= k < i ==> element != test_elements[k],
        decreases test_elements.len() - i
    {
        if element == test_elements[i] {
            return true;
        }
        i += 1;
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
{
    /* code modified by LLM (iteration 5): using corrected helper function */
    let mut result = Vec::new();
    let mut i = 0;
    while i < element.len()
        invariant
            0 <= i <= element.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> 
                (result[k] == true <==> exists|j: int| 0 <= j < test_elements.len() && element[k] == test_elements[j]),
        decreases element.len() - i
    {
        let is_contained = contains_element(element[i], &test_elements);
        result.push(is_contained);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}