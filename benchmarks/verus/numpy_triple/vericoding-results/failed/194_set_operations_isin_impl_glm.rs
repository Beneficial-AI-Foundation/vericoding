// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed loop invariants and added proper updates */
fn contains(v: &Vec<f32>, x: f32) -> (b: bool)
    ensures b == exists|j: int| 0 <= j < v.len() && v[j] == x
{
    let mut i = 0;
    let mut found = false;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            found ==> exists|j: int| 0 <= j < i && v[j] == x,
            !found ==> forall|j: int| 0 <= j < i ==> v[j] != x
        decreases v.len() - i
    {
        if !found && v[i] == x {
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
{
    /* code modified by LLM (iteration 5): fixed loop invariants and bounds checking */
    let mut result = Vec::new();
    let mut i = 0;
    while i < element.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> 
                result[k] == true <==> exists|j: int| 0 <= j < test_elements.len() && element[k] == test_elements[j]
        decreases element.len() - i
    {
        let elem = element[i];
        let found = contains(&test_elements, elem);
        result.push(found);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}