// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error with brackets for vector indexing */
fn contains_element(element: f32, test_elements: &Vec<f32>) -> (result: bool)
    ensures result == (exists|j: int| 0 <= j < test_elements.len() && element == test_elements[j])
{
    for i in 0..test_elements.len()
        invariant 
            forall|k: int| 0 <= k < i as int ==> element != test_elements[k]
    {
        if element == test_elements[i] {
            proof {
                assert(0 <= i as int < test_elements.len() && element == test_elements[i as int]);
            }
            return true;
        }
    }
    proof {
        assert(forall|k: int| 0 <= k < test_elements.len() ==> element != test_elements[k]);
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
    /* code modified by LLM (iteration 5): implementation using helper function */
    let mut result = Vec::new();
    for i in 0..element.len()
        invariant 
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> 
                (result[k] == true <==> exists|j: int| 0 <= j < test_elements.len() && element[k] == test_elements[j])
    {
        let is_present = contains_element(element[i], &test_elements);
        result.push(is_present);
    }
    result
}
// </vc-code>

}
fn main() {}