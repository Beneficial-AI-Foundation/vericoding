// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simplified existence-in-prefix predicate */
pub open spec fn exists_in_prefix(s: Seq<f32>, x: f32, k: int) -> bool {
    exists|j: int| 0 <= j < k && s[j] == x
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
    /* code modified by LLM (iteration 2): update 'found' after incrementing 'j' to maintain invariant over the examined prefix */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < element.len()
        invariant
            result.len() == i,
            i <= element.len(),
            forall|k: int| 0 <= k < i as int ==> (result[k] == true <==> exists|j: int| 0 <= j < test_elements.len() && element[k] == test_elements[j]),
        decreases element.len() - i
    {
        let xi = element[i];
        let mut found: bool = false;
        let mut j: usize = 0;
        while j < test_elements.len()
            invariant
                j <= test_elements.len(),
                (found == true) <==> (exists|jj: int| 0 <= jj < j as int && xi == test_elements[jj]),
            decreases test_elements.len() - j
        {
            let eq = xi == test_elements[j];
            j = j + 1;
            if eq {
                found = true;
            }
        }
        proof { assert(j == test_elements.len()); }
        result.push(found);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}