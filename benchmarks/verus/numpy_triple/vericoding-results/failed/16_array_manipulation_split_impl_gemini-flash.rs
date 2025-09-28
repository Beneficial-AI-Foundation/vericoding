// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split(arr: Vec<f32>, k: usize) -> (result: Vec<Vec<f32>>)
    requires
        k > 0,
        arr.len() % k == 0,
    ensures
        result.len() == k,
        forall|i: int| #[trigger] result[i].len() == (arr.len() / k) ==> (0 <= i < k),
        forall|i: int, j: int| 
            0 <= i < k && 0 <= j < (arr.len() / k) as int ==> {
                let idx = i * (arr.len() / k) as int + j;
                0 <= idx < arr.len() as int && #[trigger] result[i][j] == arr[idx]
            },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed trigger issue by converting arr_idx to int within the forall statement. */
{
    let sub_array_size = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < k
        invariant
            0 <= i <= k,
            result.len() == i,
            // All sub-arrays created so far have the correct length
            forall|idx_i: int| 0 <= idx_i < i ==> result[idx_i].len() == sub_array_size as int,
            // Elements of the sub-arrays created so far match the original array
            forall|idx_i: int, idx_j: int|
                0 <= idx_i < i && 0 <= idx_j < sub_array_size as int ==> {
                    let arr_idx: int = idx_i * sub_array_size as int + idx_j;
                    #[trigger] result[idx_i][idx_j] == arr[arr_idx]
                },
        decreases k - i
    {
        let mut sub_array: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < sub_array_size
            invariant
                0 <= j <= sub_array_size,
                sub_array.len() == j,
                // Elements added to the current sub_array match the original array
                forall|idx_j: int| 0 <= idx_j < j ==> {
                    let arr_idx: int = i * sub_array_size as int + idx_j;
                    #[trigger] sub_array[idx_j] == arr[arr_idx]
                },
            decreases sub_array_size - j
        {
            let arr_idx_usize = i * sub_array_size + j;
            sub_array.push(arr.index(arr_idx_usize as int));
            j = j + 1;
        }
        result.push(sub_array);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}