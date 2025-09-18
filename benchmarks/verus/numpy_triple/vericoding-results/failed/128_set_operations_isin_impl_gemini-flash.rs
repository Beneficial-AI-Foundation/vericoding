// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `vec_theory_nth` usage within the loop invariant to accept `int` types where appropriate. */
proof fn check_element_presence(element_val: f32, test_elements: Vec<f32>) -> (present: bool)
    ensures
        present == (exists|j: int| 0 <= j < test_elements.len() && element_val == test_elements[j])
{
    let mut present = false;
    let mut j: usize = 0;
    while j < test_elements.len()
        invariant
            j <= test_elements.len(),
            present == (exists|k: int| 0 <= k < j as int && element_val == test_elements.vec_theory_nth(k as int))
    {
        if element_val == test_elements.vec_theory_nth(j as int) {
            present = true;
        }
        j = j + 1;
    }
    present
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
/* code modified by LLM (iteration 5): Corrected `vec_theory_nth` usage within the loop invariant to accept `int` types where appropriate. */
{
    let mut result: Vec<bool> = Vec::new();
    result.reserve(element.len());

    let mut i = 0;
    while i < element.len()
        invariant
            i <= element.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> 
                (result.vec_theory_nth(k as int) == (exists|j: int| 0 <= j < test_elements.len() && element.vec_theory_nth(k as int) == test_elements.vec_theory_nth(j as int)))
    {
        let mut is_present = false;
        let mut j: usize = 0;
        while j < test_elements.len()
            invariant
                j <= test_elements.len(),
                is_present == (exists|k: int| 0 <= k < j as int && element.vec_theory_nth(i as int) == test_elements.vec_theory_nth(k as int))
        {
            if element.vec_theory_nth(i as int) == test_elements.vec_theory_nth(j as int) {
                is_present = true;
            }
            j = j + 1;
        }
        result.push(is_present);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}