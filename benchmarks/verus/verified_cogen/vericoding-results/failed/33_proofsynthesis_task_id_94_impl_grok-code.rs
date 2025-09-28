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
/* code modified by LLM (iteration 5): corrected invariant syntax by removing incorrect outer parentheses, ensuring bool expressions */
{
    let mut min_val: i32 = arr[0][1];
    let mut min_idx: usize = 0;
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            i as int <= arr.len() as int,
            0 <= min_idx as int && min_idx as int < arr.len() as int,
            forall|j: int| 0 <= j < (i as int) ==> min_val <= #[trigger] arr@[j]@[1],
            min_val == arr@[min_idx as int]@[1]
        decreases (arr.len() as int) - (i as int)
    {
        if arr[i][1] < min_val {
            min_val = arr[i][1];
            min_idx = i;
        }
        proof {
            assert(min_val <= arr@[i as int]@[1]);
        }
        i = i + 1;
    }
    arr[min_idx][0]
}
// </vc-code>

}
fn main() {}