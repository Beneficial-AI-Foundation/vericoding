// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed comparison and indexing with proper type casting */
fn isin_element(elem: f32, test_elements: &Seq<f32>) -> (found: bool)
    ensures
        found == exists|j: int| 0 <= j < test_elements.len() && elem == test_elements[j]
{
    let mut index: int = 0;
    let mut found_val = false;
    while index < test_elements.len() as int
        invariant
            0 <= index <= test_elements.len() as int,
            found_val == exists|j: int| 0 <= j < index && elem == test_elements@[j],
            forall|j: int| 0 <= j < index && !found_val ==> elem != test_elements@[j]
        decreases test_elements.len() as int - index
    {
        if elem == test_elements@[index as nat] {
            found_val = true;
        }
        index += 1;
    }
    found_val
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
/* code modified by LLM (iteration 5): Fixed indexing with proper type casting */
{
    let mut result = Vec::new();
    let mut i: int = 0;
    let element_seq = element@;
    let test_elements_seq = test_elements@;
    while i < element_seq.len() as int
        invariant
            0 <= i <= element_seq.len() as int,
            result.len() == i as nat,
            forall|k: int| 0 <= k < i ==> 
                result@[k as nat] == true <==> exists|j: int| 0 <= j < test_elements_seq.len() && element_seq@[k as nat] == test_elements_seq@[j]
        decreases element_seq.len() as int - i
    {
        let found = isin_element(element_seq@[i as nat], &test_elements_seq);
        result.push(found);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}