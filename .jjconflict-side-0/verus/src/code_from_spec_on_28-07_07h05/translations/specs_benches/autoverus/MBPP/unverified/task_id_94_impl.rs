use vstd::prelude::*;

fn main() {}

verus! {

//IMPL min_second_value_first
fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
{
    /* code modified by LLM (iteration 1): Added bounds checks and fixed array access preconditions */
    // First ensure we can access arr[0]
    assert(arr.len() > 0);
    assert(0 < arr.len());
    assert(arr[0].len() >= 2);
    assert(0 < arr[0].len() && 1 < arr[0].len());
    
    let mut min_second = arr[0][1];
    let mut result_first = arr[0][0];
    let mut min_index = 0;
    
    /* code modified by LLM (iteration 1): Fixed loop invariants and added proper bounds checking */
    for i in 1..arr.len()
        invariant
            arr.len() > 0,
            forall|k: int| 0 <= k < arr.len() ==> arr[k].len() >= 2,
            0 <= min_index < arr.len(),
            min_index < i,
            min_second == arr[min_index as int][1],
            result_first == arr[min_index as int][0],
            forall|j: int| 0 <= j < i ==> min_second <= arr[j][1],
            i <= arr.len(),
    {
        /* code modified by LLM (iteration 1): Added bounds assertions before array access */
        assert(i < arr.len());
        assert(arr[i as int].len() >= 2);
        assert(1 < arr[i as int].len());
        
        if arr[i][1] < min_second {
            min_second = arr[i][1];
            result_first = arr[i][0];
            min_index = i;
        }
    }
    
    /* code modified by LLM (iteration 1): Added final assertion to help prove postcondition */
    assert(forall|j: int| 0 <= j < arr.len() ==> min_second <= arr[j][1]);
    assert(0 <= min_index < arr.len());
    assert(result_first == arr[min_index as int][0]);
    assert(min_second == arr[min_index as int][1]);
    
    result_first
}

} // verus!