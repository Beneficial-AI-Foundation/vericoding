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
    /* code modified by LLM (iteration 3): Added explicit bounds assertions using preconditions */
    assert(arr.len() > 0);
    assert(0 < arr.len());
    assert(forall|i: int| 0 <= i < arr.len() ==> arr[i].len() >= 2);
    assert(arr[0].len() >= 2);
    
    let mut min_second = arr[0][1];
    let mut result_first = arr[0][0];
    let mut min_index = 0;
    
    let mut i = 1;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= min_index < i,
            min_index < arr.len(),
            /* code modified by LLM (iteration 3): Split chained comparison into separate conditions */
            0 <= min_index as int,
            min_index as int < arr.len(),
            arr[min_index as int].len() >= 2,
            min_second == arr[min_index as int][1],
            result_first == arr[min_index as int][0],
            forall|k: int| 0 <= k < i ==> arr[min_index as int][1] <= #[trigger] arr[k][1],
            /* code modified by LLM (iteration 3): Maintain precondition in loop invariant */
            forall|k: int| 0 <= k < arr.len() ==> arr[k].len() >= 2,
        decreases arr.len() - i
    {
        /* code modified by LLM (iteration 3): Use precondition to establish bounds */
        assert(0 <= i as int < arr.len());
        assert(forall|k: int| 0 <= k < arr.len() ==> arr[k].len() >= 2);
        assert(arr[i as int].len() >= 2);
        
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