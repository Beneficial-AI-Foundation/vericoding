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
    
    let mut k = 1;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while k < arr.len()
        invariant
            0 <= k <= arr.len(),
            0 <= min_index < k,
            min_second == arr[min_index as int][1],
            result_first == arr[min_index as int][0],
            forall|j: int| 0 <= j < k ==> arr[min_index as int][1] <= #[trigger] arr[j][1],
        decreases arr.len() - k
    {
        if arr[k][1] < min_second {
            min_second = arr[k][1];
            result_first = arr[k][0];
            min_index = k;
        }
        k += 1;
    }
    
    result_first
}

} // verus!

fn main() {}