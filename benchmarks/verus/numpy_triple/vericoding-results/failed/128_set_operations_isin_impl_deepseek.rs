// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed invariant in is_in function to properly track existence and ensure once found remains true */
fn is_in(x: f32, arr: Vec<f32>) -> (found: bool)
    ensures
        found == true <==> exists|j: int| 0 <= j < arr.len() && arr@[j] == x
{
    let mut i = 0;
    let mut found = false;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            found == true <==> exists|j: int| 0 <= j < i && arr@[j] == x,
            forall|k: int| 0 <= k < i ==> (arr@[k] == x ==> found == true)
        decreases arr.len() - i
    {
        if arr[i] == x {
            found = true;
        }
        i += 1;
    }
    found
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
/* code modified by LLM (iteration 5): Fixed loop invariant to use proper existential quantification syntax and ensure correct result tracking */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < element.len()
        invariant
            0 <= i <= element.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> 
                result@[k] == (exists|j: int| 0 <= j < test_elements.len() && element@[k] == test_elements@[j])
        decreases element.len() - i
    {
        let found = is_in(element[i], test_elements.clone());
        result.push(found);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}