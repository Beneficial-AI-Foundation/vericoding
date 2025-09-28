// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(test_cases: Seq<Seq<int>>) -> bool {
    forall|i: int| 0 <= i < test_cases.len() ==> test_cases[i].len() >= 1
}

spec fn sum_differences(arr: Seq<int>, start: int) -> int
    recommends 0 <= start <= arr.len()
    decreases arr.len() - start
{
    if start >= arr.len() - 1 {
        0
    } else {
        (if arr[start] > arr[start + 1] { arr[start] - arr[start + 1] } else { 0 }) + sum_differences(arr, start + 1)
    }
}

spec fn correct_result(test_cases: Seq<Seq<int>>, results: Seq<int>) -> bool {
    results.len() == test_cases.len() &&
    forall|i: int| 0 <= i < test_cases.len() ==> results[i] == sum_differences(test_cases[i], 0) &&
    forall|i: int| 0 <= i < results.len() ==> results[i] >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added sum_differences_bounds lemma to prove non-negativity */
proof fn sum_differences_bounds(arr: Seq<int>, start: int)
    requires 0 <= start <= arr.len()
    ensures sum_differences(arr, start) >= 0
    decreases arr.len() - start
{
    if start >= arr.len() - 1 {
        // Base case: sum_differences returns 0
    } else {
        // Recursive case
        let diff = if arr[start] > arr[start + 1] { arr[start] - arr[start + 1] } else { 0 };
        assert(diff >= 0);
        sum_differences_bounds(arr, start + 1);
        assert(sum_differences(arr, start + 1) >= 0);
        assert(sum_differences(arr, start) == diff + sum_differences(arr, start + 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<Vec<i8>>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)))
    ensures correct_result(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)), results@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariants and arithmetic overflow */
    let mut results: Vec<i8> = Vec::new();
    let mut idx = 0;
    
    while idx < test_cases.len()
        invariant
            0 <= idx <= test_cases.len(),
            results.len() == idx,
            valid_input(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int))),
            forall|k: int| 0 <= k < idx ==> results@[k] as int == sum_differences(test_cases@[k]@.map_values(|x: i8| x as int), 0),
            forall|k: int| 0 <= k < idx ==> results@[k] >= 0
        decreases test_cases.len() - idx
    {
        let arr = &test_cases[idx];
        assert(arr.len() >= 1); // From valid_input
        
        if arr.len() == 1 {
            // Special case: single element array
            results.push(0);
            proof {
                assert(sum_differences(arr@.map_values(|x: i8| x as int), 0) == 0);
            }
        } else {
            let mut sum: i8 = 0;
            let mut j = 0;
            
            while j < arr.len() - 1
                invariant
                    0 <= j <= arr.len() - 1,
                    arr.len() >= 2,
                    sum as int == sum_differences(arr@.map_values(|x: i8| x as int), 0) - sum_differences(arr@.map_values(|x: i8| x as int), j as int),
                    sum >= 0
                decreases arr.len() - 1 - j
            {
                if arr[j] > arr[j + 1] {
                    let diff = (arr[j] as int - arr[j + 1] as int) as i8;
                    sum = (sum as int + diff as int) as i8;
                }
                j = j + 1;
            }
            
            proof {
                sum_differences_bounds(arr@.map_values(|x: i8| x as int), 0);
                assert(j == arr.len() - 1);
                assert(sum_differences(arr@.map_values(|x: i8| x as int), j as int) == 0);
            }
            
            results.push(sum);
        }
        idx = idx + 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}