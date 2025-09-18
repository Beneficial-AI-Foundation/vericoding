// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed */
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
/* code modified by LLM (iteration 5): Fix `usize` and `int` type mismatches in index operations and assertions. */
{
    let sub_array_len_usize = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut i = 0;
    while i < k
        invariant
            result.len() == i,
            forall|l: int| 0 <= l < i ==> result[l as usize].len() == sub_array_len_usize,
            forall|l: int, m: int|
                0 <= l < i && (m as usize) < sub_array_len_usize ==> {
                    let idx = (l * sub_array_len_usize as int) + m;
                    (idx as usize) < arr.len() && result[l as usize][m as usize] == arr[idx as usize]
                },
            i <= k,
    {
        let mut sub_array: Vec<f32> = Vec::new();
        let mut j = 0;
        while j < sub_array_len_usize
            invariant
                sub_array.len() == j,
                forall|m: int| (m as usize) < j ==> {
                    let current_idx_in_arr = (i * sub_array_len_usize) + (m as usize);
                    current_idx_in_arr < arr.len() && sub_array[m as usize] == arr[current_idx_in_arr]
                },
                j <= sub_array_len_usize,
        {
            let idx_in_arr = i * sub_array_len_usize + j;
            sub_array.push(arr[idx_in_arr]);
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