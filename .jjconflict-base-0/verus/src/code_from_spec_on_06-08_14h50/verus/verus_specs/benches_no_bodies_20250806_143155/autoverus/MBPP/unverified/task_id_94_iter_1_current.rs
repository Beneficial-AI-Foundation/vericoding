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
    let mut min_idx = 0;
    
    for i in 1..arr.len()
        invariant
            0 <= min_idx < arr.len(),
            min_second == arr[min_idx][1],
            result_first == arr[min_idx][0],
            forall|j: int| 0 <= j < i ==> min_second <= arr[j][1],
    {
        if arr[i][1] < min_second {
            min_second = arr[i][1];
            result_first = arr[i][0];
            min_idx = i;
        }
    }
    
    result_first
}

} // verus!