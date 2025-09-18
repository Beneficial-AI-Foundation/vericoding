// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn seq_contains(s: Seq<f32>, e: f32) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == e
}

/* helper modified by LLM (iteration 5): added assertions to prove postconditions and removed unnecessary reveal calls */
fn vec_contains(test_elements: &Vec<f32>, elem: f32) -> (result: bool)
    ensures result == seq_contains(test_elements.view(), elem)
{
    let mut i: usize = 0;
    while i < test_elements.len()
        invariant
            forall|j: int| 0 <= j < i ==> test_elements.view()[j] != elem,
        decreases test_elements.len() - i
    {
        if test_elements[i] == elem {
            assert(seq_contains(test_elements.view(), elem));
            return true;
        }
        i = i + 1;
    }
    assert(!seq_contains(test_elements.view(), elem));
    return false;
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
    /* code modified by LLM (iteration 5): removed unnecessary proof block with reveal call */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < element.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> 
                (result@[k] <==> seq_contains(test_elements.view(), element@[k])),
        decreases element.len() - i
    {
        let is_in = vec_contains(&test_elements, element[i]);
        result.push(is_in);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}