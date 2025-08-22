use vstd::prelude::*;

verus! {

//IMPL min_second_value_first
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
    /* code modified by LLM (iteration 2): proper bounds checking and initialization */
    let mut min_second = arr[0][1];
    let mut result_first = arr[0][0];
    let mut min_index: usize = 0;
    
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= min_index < i,
            min_index < arr.len(),
            /* code modified by LLM (iteration 2): ensure bounds are properly established */
            forall|k: int| 0 <= k < arr.len() ==> arr[k].len() >= 2,
            min_second == arr[min_index][1],
            result_first == arr[min_index][0],
            /* code modified by LLM (iteration 2): simplified forall with proper bounds */
            forall|k: int| 0 <= k < i ==> arr[min_index][1] <= arr[k][1],
        decreases arr.len() - i
    {
        /* code modified by LLM (iteration 2): removed problematic assertion and use direct access */
        if arr[i][1] < min_second {
            min_second = arr[i][1];
            result_first = arr[i][0];
            min_index = i;
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 2): helper assertion to establish final postcondition */
    assert(forall|k: int| 0 <= k < arr.len() ==> arr[min_index][1] <= arr[k][1]) by {
        assert(forall|k: int| 0 <= k < arr.len() ==> arr[min_index][1] <= arr[k][1]);
    }
    
    result_first
}

} // verus!

fn main() {}