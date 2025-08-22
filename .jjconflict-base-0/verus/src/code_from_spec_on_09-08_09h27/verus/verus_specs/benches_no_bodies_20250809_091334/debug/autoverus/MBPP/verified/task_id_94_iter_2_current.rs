use vstd::prelude::*;

fn main() {
    // Example usage
    let arr = vec![
        vec![10, 5],
        vec![20, 3],
        vec![30, 7],
    ];
    let result = min_second_value_first(&arr);
    println!("Result: {}", result); // Should print 20, since [20, 3] has minimum second value 3
}

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
    let mut min_idx = 0;
    let mut i = 1;
    
    while i < arr.len()
        invariant
            0 <= min_idx < arr.len(),
            1 <= i <= arr.len(),
            /* code modified by LLM (iteration 1): fixed type mismatch by casting min_idx to int */
            forall|k: int| 0 <= k < i ==> arr[min_idx as int][1] <= #[trigger] arr[k][1],
    {
        if arr[i][1] < arr[min_idx][1] {
            min_idx = i;
        }
        i += 1;
    }
    
    arr[min_idx][0]
}

} // verus!