use vstd::prelude::*;

verus! {

fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
    // post-conditions-end
{
    let mut min_second = arr[0][1];
    let mut result_first = arr[0][0];
    let mut min_index = 0;
    
    let mut i = 1;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= min_index < i,
            min_second == arr[min_index as int][1],
            result_first == arr[min_index as int][0],
            forall|k: int| 0 <= k < i ==> min_second <= #[trigger] arr[k][1],
    {
        if arr[i][1] < min_second {
            min_second = arr[i][1];
            result_first = arr[i][0];
            min_index = i;
        }
        i += 1;
    }
    
    result_first
}

} // verus!

fn main() {}