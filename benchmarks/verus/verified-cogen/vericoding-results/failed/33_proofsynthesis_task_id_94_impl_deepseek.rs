// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatches by using proper vector indexing syntax with @ */
proof fn find_min_index_proof(arr: &Vec<Vec<i32>>) -> (min_index: usize)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    ensures
        0 <= min_index < arr.len(),
        forall|j: int| 0 <= j < arr.len() ==> arr@[min_index][1] <= arr@[j][1]
{
    let mut min_index: usize = 0;
    let mut i: usize = 1;

    while i < arr.len()
        invariant
            0 <= min_index < arr.len(),
            1 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> arr@[min_index][1] <= arr@[k][1]
        decreases(arr.len() - i)
    {
        if arr@[i][1] < arr@[min_index][1] {
            min_index = i;
        }
        i = i + 1;
    }
    min_index
}

fn find_min_index_exec(arr: &Vec<Vec<i32>>) -> (min_index: usize)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    ensures
        0 <= min_index < arr.len(),
        forall|j: int| 0 <= j < arr.len() ==> arr@[min_index][1] <= arr@[j][1]
{
    let mut min_index: usize = 0;
    let mut i: usize = 1;

    while i < arr.len()
        invariant
            0 <= min_index < arr.len(),
            1 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> arr@[min_index][1] <= arr@[k][1]
        decreases(arr.len() - i)
    {
        if arr@[i][1] < arr@[min_index][1] {
            min_index = i;
        }
        i = i + 1;
    }
    min_index
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
/* code modified by LLM (iteration 5): Fixed by using proper vector indexing syntax with @ */
{
    let min_index: usize = find_min_index_exec(arr);
    arr@[min_index][0]
}
// </vc-code>

}
fn main() {}