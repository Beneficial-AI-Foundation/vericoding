// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use @ indexing for Vec and int indices */
spec fn vec_contains(elem: f32, v: Vec<f32>) -> bool { exists|i: int| 0 <= i && i < v.len() && elem == v@[i] }
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
    /* code modified by LLM (iteration 5): implement numpy_isin using helper vec_contains and int indices */
    let mut result_vec: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < element.len()
        invariant 0 <= i && i <= element.len(),
        invariant result_vec.len() == i,
        invariant forall|k: int| 0 <= k && k < i ==> (result_vec@[k] == vec_contains(element@[k], test_elements)),
        decreases element.len() - i
    {
        let mut found: bool = false;
        let mut j: int = 0;
        while j < test_elements.len()
            invariant 0 <= j && j <= test_elements.len(),
            invariant found == (exists|k: int| 0 <= k && k < j && element@[i] == test_elements@[k]),
            decreases test_elements.len() - j
        {
            if element@[i] == test_elements@[j] {
                found = true;
            }
            j = j + 1;
        }
        proof {
            assert(found == vec_contains(element@[i], test_elements));
        }
        result_vec.push(found);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}