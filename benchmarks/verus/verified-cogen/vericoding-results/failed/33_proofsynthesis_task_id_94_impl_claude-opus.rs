// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn has_min_second(arr: &Vec<Vec<i32>>, idx: int) -> bool
    recommends
        0 <= idx < arr.len(),
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> arr[i].len() >= 2,
{
    forall|j: int| 0 <= j < arr.len() ==> arr[idx][1] <= arr[j][1]
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
{
    /* code modified by LLM (iteration 5): fixed type mismatch by casting min_idx to int in invariant */
    let mut min_idx: usize = 0;
    let mut min_second = arr[0][1];
    
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            0 <= min_idx < i <= arr.len(),
            min_second == arr[min_idx as int][1],
            forall|j: int| 0 <= j < i ==> arr[min_idx as int][1] <= arr[j][1],
        decreases arr.len() - i
    {
        if arr[i][1] < min_second {
            min_second = arr[i][1];
            min_idx = i;
        }
        i = i + 1;
    }
    
    arr[min_idx][0]
}
// </vc-code>

}
fn main() {}