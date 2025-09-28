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
proof fn sum_differences_matches_loop(arr: Seq<int>, start: int, end: int, accumulated: int)
    requires
        0 <= start <= end <= arr.len(),
        accumulated >= 0
    ensures
        accumulated + sum_differences(arr, start) >= 0
{
}

fn compute_sum_differences(arr: &Vec<i8>) -> (result: i8)
    requires
        arr@.len() >= 1,
        forall|i: int| 0 <= i < arr@.len() ==> -128 <= arr@[i] <= 127
    ensures
        result as int == sum_differences(arr@.map_values(|x: i8| x as int), 0),
        result >= 0
{
    let mut sum: i8 = 0;
    let mut i: usize = 0;
    
    while i < arr.len() - 1
        invariant
            0 <= i <= arr@.len() - 1,
            sum >= 0,
            sum as int == sum_differences(arr@.map_values(|x: i8| x as int), 0) - sum_differences(arr@.map_values(|x: i8| x as int), i as int)
        decreases arr@.len() - 1 - i
    {
        let diff = if arr[i] > arr[i + 1] {
            arr[i] - arr[i + 1]
        } else {
            0
        };
        sum = sum + diff;
        i = i + 1;
    }
    
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<Vec<i8>>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)))
    ensures correct_result(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)), results@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax error with proper conditional placement */
    let mut results: Vec<i8> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < test_cases.len()
        invariant
            0 <= idx <= test_cases@.len(),
            results@.len() == idx,
            forall|i: int| 0 <= i < idx ==> #[trigger] results@[i] >= 0 && results@[i] as int == sum_differences(test_cases@[i]@.map_values(|x: i8| x as int), 0),
            forall|i: int| 0 <= i < results@.len() ==> results@[i] >= 0
        decreases test_cases@.len() - idx
    {
        let sum_diff = compute_sum_differences(&test_cases[idx]);
        results.push(sum_diff);
        idx = idx + 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}