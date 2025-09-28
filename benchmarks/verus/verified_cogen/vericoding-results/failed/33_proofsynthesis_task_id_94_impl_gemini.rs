// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 4): adding function preconditions to loop invariants */
    let mut min_idx: usize = 0;
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            arr.len() > 0,
            forall|j: int| 0 <= j < arr.len() ==> #[trigger] arr[j].len() >= 2,
            1 <= i <= arr.len(),
            0 <= min_idx < i,
            forall|k: int| 0 <= k < i ==> arr[min_idx as int][1] <= arr[k as int][1],
        decreases arr.len() - i,
    {
        if arr[i][1] < arr[min_idx][1] {
            min_idx = i;
        }
        i = i + 1;
    }
    arr[min_idx][0]
}
// </vc-code>

}
fn main() {}