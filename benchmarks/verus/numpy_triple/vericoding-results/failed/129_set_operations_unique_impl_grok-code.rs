// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn unique(arr: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < j < result.len() ==> result[i] < result[j],

        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> exists|j: int| 0 <= j < arr.len() && result[i] == arr[j],

        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> result[i] != result[j],

        forall|i: int| #![trigger arr[i]] 0 <= i < arr.len() ==> exists|j: int| 0 <= j < result.len() && arr[i] == result[j],
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Added decreases clauses to all while loops to ensure termination */
    let mut unique_vals = Vec::new();
    let arr_len = arr.len();
    let mut arr_index = 0;
    while arr_index < arr_len
    decreases arr_len - arr_index
    {
        let a = arr[arr_index];
        // check if a is already in unique_vals
        let mut found = false;
        let unique_len = unique_vals.len();
        let mut unique_index = 0;
        while unique_index < unique_len
        decreases unique_len - unique_index
        {
            if unique_vals[unique_index] == a {
                found = true;
                break;
            }
            unique_index += 1;
        }
        if !found {
            unique_vals.push(a);
        }
        arr_index += 1;
    }
    // now sort unique_vals using selection sort
    let mut sorted = Vec::new();
    while unique_vals.len() > 0
    decreases unique_vals.len()
    {
        let mut min_index = 0;
        let mut min_val = unique_vals[0];
        let mut i = 1;
        while i < unique_vals.len()
        decreases unique_vals.len() - i
        {
            if unique_vals[i] < min_val {
                min_index = i;
                min_val = unique_vals[i];
            }
            i += 1;
        }
        sorted.push(min_val);
        unique_vals.remove(min_index);
    }
    sorted
}
// </vc-code>

}
fn main() {}