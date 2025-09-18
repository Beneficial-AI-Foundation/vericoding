// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): unchanged */
spec fn contains(v: Vec<f32>, x: f32) -> bool {
        exists|i: int| 0 <= i < (v.len() as int) && v@[i] == x
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
        /* code modified by LLM (iteration 5): fixed invariant_except_break syntax by adding curly braces */
        let mut result = Vec::new();
        let n = element.len();
        for i in 0..n
            invariant
                result.len() == i,
                (i as int) < element.len(),
                forall|k: int| 0 <= k < (i as int) ==> #[trigger] result@[k] == contains(test_elements, element@[k])
        {
            let mut found = false;
            let m = test_elements.len();
            for j in 0..m
                invariant_except_break {
                    0 <= (j as int) < test_elements.len(),
                    found == (exists|k: int| 0 <= k < (j as int) && element@[i as int] == test_elements@[k])
                }
            {
                if element[i] == test_elements[j] {
                    found = true;
                    break;
                }
            }
            result.push(found);
        }
        result
    }
// </vc-code>

}
fn main() {}