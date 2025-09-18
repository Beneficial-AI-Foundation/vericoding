// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains(value: f32, arr: Vec<f32>) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] == value
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
    let mut result: Vec<bool> = Vec::new();
    for i in 0..element.len()
        invariant i <= element.len()
        invariant result.len() == i
        invariant forall |k: int| 0 <= k < i ==> result[k] == contains(element[k], test_elements) {
        let mut found = false;
        for j in 0..test_elements.len()
            invariant j <= test_elements.len()
            invariant found == exists |l: int| 0 <= l < j && element[i] == test_elements[l] {
            if element[i] == test_elements[j] {
                found = true;
                break;
            }
            j += 1;
        }
        result.push(found);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}