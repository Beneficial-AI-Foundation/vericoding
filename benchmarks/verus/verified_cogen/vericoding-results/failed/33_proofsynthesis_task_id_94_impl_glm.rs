// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): converted spec function to exec function to avoid compilation error */
exec fn get_second(arr: &Vec<Vec<i32>>, i: int) -> (result: i32)
    requires 0 <= i < arr@.len() && arr@[i].len() >= 2,
    ensures result == arr@[i][1],
{
    arr[i as usize][1]
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
/* code modified by LLM (iteration 5): simplified implementation to directly find min value without helper function */
{
    let mut min_index: usize = 0;
    let mut min_second_value = arr[0][1];
    for i in 1..arr.len()
        invariant
            min_index < arr.len(),
            min_second_value == arr[min_index][1],
            forall|j: int| 0 <= j < i as int ==> min_second_value <= arr[j as usize][1],
    {
        let current_second = arr[i][1];
        if current_second < min_second_value {
            min_index = i;
            min_second_value = current_second;
        }
    }
    arr[min_index][0]
}
// </vc-code>

}
fn main() {}