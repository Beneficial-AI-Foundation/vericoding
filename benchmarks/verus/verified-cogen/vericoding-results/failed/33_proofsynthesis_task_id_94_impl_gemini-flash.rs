// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected implementation of min_second_value_helper to find the index of the minimum second value. */
spec fn min_second_value_helper(arr: &Vec<Vec<i32>>) -> int
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    ensures
        0 <= min_second_value_helper(arr) < arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> arr[min_second_value_helper(arr) as int][1] <= arr[i as int][1],
{
    if arr.len() == 1 {
        0
    } else {
        let mut min_val_index: int = 0;
        let mut i: int = 1;
        while i < arr.len()
            invariant
                0 < i <= arr.len(),
                0 <= min_val_index < i,
                forall|k: int| 0 <= k < i ==> arr[min_val_index][1] <= arr[k][1],
        {
            if arr[i][1] < arr[min_val_index][1] {
                min_val_index = i;
            }
            i = i + 1;
        }
        min_val_index
    }
}
// </vc-helpers>

// <vc-spec>
fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,

    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Ensured that types are consistent for array indexing to fix compilation error. */
{
    let min_idx_int = min_second_value_helper(arr);
    arr[min_idx_int as int][0]
}
// </vc-code>

}
fn main() {}