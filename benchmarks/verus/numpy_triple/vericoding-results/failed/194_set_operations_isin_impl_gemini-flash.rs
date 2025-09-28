// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `is_in` helper had a compilation error due to `test_elements[j]` not being allowed. The fix replaces `test_elements[j]` with `@test_elements[j]` to conform to Verus’s indexing requirements for sequences/vectors in quantifiers. */
proof fn is_in(val: f32, test_elements: &Vec<f32>) -> (ret: bool)
    ensures
        ret == (exists|j: int| 0 <= j < test_elements.len() && val == test_elements@[j])
{
    let mut i: int = 0;
    let mut found: bool = false;

    while i < test_elements.len()
        invariant
            0 <= i <= test_elements.len(),
            found == (exists|j: int| 0 <= j < i && val == test_elements@[j])
        decreases test_elements.len() - i
    {
        proof {
            if !found && exists|k: int| 0 <= k < test_elements.len() && val == test_elements@[k] {
                let k_val = choose|k: int| 0 <= k < test_elements.len() && val == test_elements@[k];
                if k_val < i {
                    assert(exists|j: int| 0 <= j < i && val == test_elements@[j]);
                }
            }
        }
        if val == test_elements@[i] {
            found = true;
        }
        i = i + 1;
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
/* code modified by LLM (iteration 5): The main numpy_isin function had a compilation error with `element[k]` in the invariant; it's corrected to `element@[k]` to properly index the vector as a sequence. */
{
    let mut result: Vec<bool> = Vec::with_capacity(element.len());
    let mut i: int = 0;

    while i < element.len() as int
        invariant
            0 <= i <= element.len() as int,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> (result@[k] == true <==> exists|j: int| 0 <= j < test_elements.len() && element@[k] == test_elements@[j])
        decreases element.len() as int - i
    {
        let val_found = is_in(element@[i], &test_elements);
        result.push(val_found);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}