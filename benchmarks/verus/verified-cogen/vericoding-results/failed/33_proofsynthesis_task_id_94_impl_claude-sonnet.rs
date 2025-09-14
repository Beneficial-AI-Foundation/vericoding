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
    /* code modified by LLM (iteration 5): Added decreases clause to fix compilation error */
    let mut min_second = arr[0][1];
    let mut result = arr[0][0];
    let mut min_index = 0;
    
    let mut i = 1;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= min_index < i,
            min_second == arr@[min_index as int]@[1],
            result == arr@[min_index as int]@[0],
            forall|j: int| 0 <= j < i ==> arr@[min_index as int]@[1] <= arr@[j]@[1],
        decreases arr.len() - i
    {
        if arr[i][1] < min_second {
            min_second = arr[i][1];
            result = arr[i][0];
            min_index = i;
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}