// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use usize indices consistent with Vec indexing */
fn vec_contains(test_elements: &Vec<f32>, x: f32) -> (res: bool)
    ensures
        res == (exists|j: usize| j < test_elements.len() && test_elements[j] == x),
{
    let mut i: usize = 0;
    let mut found: bool = false;
    while i < test_elements.len() && !found
        invariant
            i <= test_elements.len(),
            found == (exists|j: usize| j < i && test_elements[j] == x),
        decreases test_elements.len() - i
    {
        if test_elements[i] == x {
            found = true;
        } else {
            i = i + 1;
        }
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
{
    /* code modified by LLM (iteration 5): iterate using usize indices and use vec_contains helper */
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < element.len()
        invariant
            i <= element.len(),
            res.len() == i,
            forall|k: usize| k < i ==> (res[k] == true <==> exists|j: usize| j < test_elements.len() && element[k] == test_elements[j]),
        decreases element.len() - i
    {
        let contains = vec_contains(&test_elements, element[i]);
        assert(contains == (exists|j: usize| j < test_elements.len() && test_elements[j] == element[i]));
        res.push(contains);
        i = i + 1;
    }
    res
}

// </vc-code>

}
fn main() {}