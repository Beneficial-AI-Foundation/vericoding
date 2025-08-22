use vstd::prelude::*;

fn main() {
    let test_arr = vec![
        vec![10, 5],
        vec![20, 3], 
        vec![30, 7]
    ];
    let result = min_second_value_first(&test_arr);
    println!("Result: {}", result); // Should print 20
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
    let mut min_index: usize = 0;
    let mut min_second_value = arr[0][1];
    
    let mut k: usize = 1;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while k < arr.len()
        invariant
            0 <= min_index < arr.len(),
            min_second_value == arr[min_index as int][1],
            forall|i: int| 0 <= i < k ==> arr[min_index as int][1] <= arr[i][1],
            k <= arr.len(),
        decreases arr.len() - k
    {
        if arr[k][1] < min_second_value {
            min_index = k;
            min_second_value = arr[k][1];
        }
        k += 1;
    }
    
    arr[min_index][0]
}

} // verus!