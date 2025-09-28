// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains<T>(v: &Vec<T>, x: T) -> bool
    where T: View + std::cmp::PartialEq
{
    exists|i: int| 0 <= i < v.len() && v@[i] == x
}
/* helper modified by LLM (iteration 5): fixed contains function definition */
// </vc-helpers>

// <vc-spec>
fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
// </vc-spec>
// <vc-code>
{ /* code modified by LLM (iteration 5): fixed loop invariants using invariant_except_break */
    let mut result = Vec::new();
    
    // Add elements from arr1 that are not in arr2
    for i in 0..arr1.len()
        invariant
            forall|j: int| 0 <= j < i ==> (!contains(arr2, arr1[j]) ==> contains(&result, arr1[j])),
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
    {
        let element = arr1[i];
        
        // Check if element is in arr2
        let mut in_arr2 = false;
        for j in 0..arr2.len()
            invariant
                0 <= j <= arr2.len(),
            invariant_except_break
                !in_arr2 ==> forall|k: int| 0 <= k < j ==> arr2[k] != element,
        {
            if element == arr2[j] {
                in_arr2 = true;
                break;
            }
        }
        
        // If not in arr2, check if it's already in result
        if !in_arr2 {
            let mut in_result = false;
            for k in 0..result.len()
                invariant
                    0 <= k <= result.len(),
                invariant_except_break
                    !in_result ==> forall|l: int| 0 <= l < k ==> result[l] != element,
            {
                if element == result[k] {
                    in_result = true;
                    break;
                }
            }
            
            // Add to result if not already there
            if !in_result {
                result.push(element);
                // Maintain uniqueness invariant
                assert(forall|j: int, k: int| 0 <= j < k < (result.len() - 1) ==> result[j] != result[k]);
            }
        }
    }
    
    // Add elements from arr2 that are not in arr1
    for i in 0..arr2.len()
        invariant
            forall|j: int| 0 <= j < arr1.len() ==> (!contains(arr2, arr1[j]) ==> contains(&result, arr1[j])),
            forall|j: int| 0 <= j < i ==> (!contains(arr1, arr2[j]) ==> contains(&result, arr2[j])),
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
    {
        let element = arr2[i];
        
        // Check if element is in arr1
        let mut in_arr1 = false;
        for j in 0..arr1.len()
            invariant
                0 <= j <= arr1.len(),
            invariant_except_break
                !in_arr1 ==> forall|k: int| 0 <= k < j ==> arr1[k] != element,
        {
            if element == arr1[j] {
                in_arr1 = true;
                break;
            }
        }
        
        // If not in arr1, check if it's already in result
        if !in_arr1 {
            let mut in_result = false;
            for k in 0..result.len()
                invariant
                    0 <= k <= result.len(),
                invariant_except_break
                    !in_result ==> forall|l: int| 0 <= l < k ==> result[l] != element,
            {
                if element == result[k] {
                    in_result = true;
                    break;
                }
            }
            
            // Add to result if not already there
            if !in_result {
                result.push(element);
                // Maintain uniqueness invariant
                assert(forall|j: int, k: int| 0 <= j < k < (result.len() - 1) ==> result[j] != result[k]);
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}