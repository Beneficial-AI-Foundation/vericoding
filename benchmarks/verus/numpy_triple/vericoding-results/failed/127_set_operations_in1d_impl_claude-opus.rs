// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed element_in_array to use indexing properly */
fn element_in_array<T: PartialEq>(element: &T, arr: &Vec<T>, arr_len: usize) -> (found: bool)
    requires arr_len <= arr.len()
    ensures found == exists|j: int| 0 <= j < arr_len && arr@[j] == *element
    decreases arr_len
{
    if arr_len == 0 {
        false
    } else if arr@[(arr_len - 1) as int] == *element {
        true
    } else {
        element_in_array(element, arr, (arr_len - 1) as usize)
    }
}
// </vc-helpers>

// <vc-spec>
fn in1d<T: PartialEq>(ar1: Vec<T>, ar2: Vec<T>) -> (result: Vec<bool>)
    ensures 
        result.len() == ar1.len(),
        forall|i: int| 0 <= i < ar1.len() ==> 
            result[i] == exists|j: int| 0 <= j < ar2.len() && ar1[i] == ar2[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Updated to use @ for sequence access */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < ar1.len()
        invariant
            i <= ar1.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] == exists|j: int| 0 <= j < ar2.len() && ar1@[k] == ar2@[j]
        decreases ar1.len() - i
    {
        let found = element_in_array(&ar1@[i as int], &ar2, ar2.len());
        result.push(found);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}