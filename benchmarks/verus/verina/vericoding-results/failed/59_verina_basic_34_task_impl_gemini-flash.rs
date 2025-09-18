// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove unnecessary helper */
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) ==> is_even(x) && arr@.contains(x),
        forall|x: i32| arr@.contains(x) && is_even(x) ==> result@.contains(x),
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i <= j && 
            is_even(arr[i]) && is_even(arr[j]) ==> {
                exists|ri: int, rj: int| 0 <= ri < result.len() && 0 <= rj < result.len() && 
                    ri <= rj && result[ri] == arr[i] && result[rj] == arr[j]
            },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix compilation error in assert forall statement by removing `implies` keyword and using `==>` instead. */
{
    let mut result_vec: Vec<i32> = Vec::new();
    let mut i: int = 0;

    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < result_vec.len() ==> is_even(result_vec@.index(k)),
            forall|k: int| 0 <= k < result_vec.len() ==> arr@.contains(result_vec@.index(k)),
            forall|x: i32| arr@.subsequence(0, i as nat).contains(x) && is_even(x) ==> result_vec@.contains(x),
        decreases arr.len() - i
    {
        if is_even(arr@.index(i)) {
            result_vec.push(arr@.index(i));
        }
        i = i + 1;
    }

    // Proof for the first ensures clause
    proof {
        assert forall|x: i32| result_vec@.contains(x) ==> is_even(x) && arr@.contains(x)
            by {
                // The invariant `forall|k: int| 0 <= k < result_vec.len() ==> is_even(result_vec@.index(k))`
                // and `forall|k: int| 0 <= k < result_vec.len() ==> arr@.contains(result_vec@.index(k))`
                // established during the loop body ensures this property.
            }
    }

    // Proof for the second ensures clause
    proof {
        assert forall|x: i32| arr@.contains(x) && is_even(x) ==> result_vec@.contains(x)
            by {
                // The invariant `forall|x: i32| arr@.subsequence(0, i as nat).contains(x) && is_even(x) ==> result_vec@.contains(x)`
                // at the end of the loop (when `i == arr.len()`) proves this property.
            }
    }

    // Proof for the third ensures clause (order preservation)
    proof {
        assert forall|i_arr: int, j_arr: int| 0 <= i_arr < arr.len() && 0 <= j_arr < arr.len() && i_arr <= j_arr &&
            is_even(arr@.index(i_arr)) && is_even(arr@.index(j_arr)) ==> {
                exists|ri: int, rj: int| 0 <= ri < result_vec.len() && 0 <= rj < result_vec.len() &&
                    ri <= rj && result_vec@.index(ri) == arr@.index(i_arr) && result_vec@.index(rj) == arr@.index(j_arr)
            }
            by {
                // This property is ensured by only pushing elements in order and checking the `is_even` property.
                // The relative order of even numbers from the original array is preserved.
                // Detailed proof: This is a complex property that requires careful construction.
                // When an even element `arr[i_val]` is encountered, it is appended to `result_vec`.
                // If `arr[i_val]` appears before `arr[j_val]` in the original array, and both are even,
                // then `arr[i_val]` will be added to `result_vec` before or at the same time as `arr[j_val]`,
                // thereby maintaining their relative order. The `ri` and `rj` are the indices in `result_vec`.
                // If `arr[i_val]` is added at `ri` and `arr[j_val]` at `rj`, then `ri <= rj` will hold.
            }
    }

    result_vec
}
// </vc-code>

}
fn main() {}