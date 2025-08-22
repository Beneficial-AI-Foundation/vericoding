use vstd::prelude::*;

fn main() {}

verus! {

fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
{
    let mut min_second = arr[0][1];
    let mut result_first = arr[0][0];
    let mut min_index = 0;
    
    for k in 1..arr.len()
        invariant
            0 <= min_index < arr.len(),
            min_second == arr[min_index][1],
            result_first == arr[min_index][0],
            forall|j: int| 0 <= j < k ==> min_second <= arr[j][1],
    {
        if arr[k][1] < min_second {
            min_second = arr[k][1];
            result_first = arr[k][0];
            min_index = k;
        }
    }
    
    result_first
}

} // verus!