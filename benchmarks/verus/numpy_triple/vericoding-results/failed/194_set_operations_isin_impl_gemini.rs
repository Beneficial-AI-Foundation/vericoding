// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): broadcast lemma is unchanged */
#[verifier::broadcast]
proof fn lemma_witness_existence(s: Seq<f32>, e: f32, i: int)
    requires
        0 <= i < s.len(),
        s[i] == e,
    ensures
        exists|j: int| 0 <= j < s.len() && s[j] == e,
{}

/* helper modified by LLM (iteration 5): wrapped lemma call in proof block to fix ghost code error */
fn contains(e: f32, v: &Vec<f32>) -> (found: bool)
    ensures
        found == true <==> (exists|j: int| 0 <= j < v.len() && v[j] == e),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|k: int| 0 <= k < i ==> v[k] != e,
        decreases v.len() - i,
    {
        if v[i] == e {
            proof {
                lemma_witness_existence(v.view(), e, i as int);
            }
            return true;
        }
        i = i + 1;
    }
    false
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
/* code modified by LLM (iteration 5): no changes needed, fix is in helper function */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < element.len()
        invariant
            0 <= i <= element.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> 
                (result[k] == true <==> exists|j: int| 0 <= j < test_elements.len() && element[k] == test_elements[j]),
        decreases element.len() - i,
    {
        let e = element[i];
        let found = contains(e, &test_elements);
        result.push(found);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}