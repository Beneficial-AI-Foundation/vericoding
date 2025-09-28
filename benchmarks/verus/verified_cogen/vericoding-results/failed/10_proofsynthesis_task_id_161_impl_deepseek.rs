// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed invariant syntax with braces and added proper verification helpers */
spec fn contains_vec(vec: Seq<i32>, elem: i32) -> bool {
    exists|i: int| 0 <= i < vec.len() && vec[i] == elem
}

spec fn remove_element(seq: Seq<i32>, elem: i32) -> Seq<i32> {
    seq.filter(|x| x != elem)
}

proof fn lemma_vec_to_seq_contains_equivalence(vec: &Vec<i32>, elem: i32)
    ensures
        vec@.contains(elem) == contains_vec(vec@, elem),
{
}

proof fn lemma_remove_element_preserves_other_elems(seq: Seq<i32>, elem: i32, other_elem: i32)
    requires
        other_elem != elem,
    ensures
        contains_vec(seq, other_elem) == contains_vec(remove_element(seq, elem), other_elem),
{
}
// </vc-helpers>

// <vc-spec>
fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed invariant syntax with proper braces */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr1.len()
        decreases arr1.len() - i,
        invariant {
            forall|j: int| 0 <= j < result@.len() ==> (arr1@.contains(result@[j]) && !arr2@.contains(result@[j])),
            forall|j: int| 0 <= j < i ==> (arr2@.contains(arr1@[j]) || result@.contains(arr1@[j])),
            i <= arr1.len(),
        }
    {
        let elem = arr1[i];
        
        // Manually check if element is in arr2 to avoid unsupported contains() method
        let mut found_in_arr2 = false;
        let mut j: usize = 0;
        while j < arr2.len()
            decreases arr2.len() - j,
            invariant {
                j <= arr2.len(),
                found_in_arr2 == (exists|k: int| 0 <= k < j && arr2@[k] == elem),
            }
        {
            if arr2[j] == elem {
                found_in_arr2 = true;
                break;
            }
            j += 1;
        }
        
        if !found_in_arr2 {
            result.push(elem);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}