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
/* helper modified by LLM (iteration 5): Fixed type conversion in lemma signature to use usize */
proof fn lemma_vec_index_valid<T>(vec: &Vec<T>, i: usize)
    requires 0 <= i < vec.len()
    ensures vec[i] == vec@[i as int]
{
}

fn calculate_sum_differences(arr: &Vec<i8>) -> (result: i8)
    ensures
        result as int == sum_differences(arr@.map_values(|x: i8| x as int), 0),
        result >= 0,
{
    let mut sum: i8 = 0;
    let mut i: usize = 0;
    while i < arr.len() - 1
        invariant
            0 <= i <= arr.len(),
            sum as int == sum_differences(arr@.map_values(|x: i8| x as int), 0) - sum_differences(arr@.map_values(|x: i8| x as int), i as int),
            sum >= 0,
        decreases arr.len() - i,
    {
        proof { lemma_vec_index_valid(arr, i); lemma_vec_index_valid(arr, i + 1); }
        let arr_i = arr[i];
        let arr_i_plus_1 = arr[i + 1];
        let diff = if arr_i > arr_i_plus_1 { arr_i - arr_i_plus_1 } else { 0 };
        proof {
            assert(sum_differences(arr@.map_values(|x: i8| x as int), i as int) == 
                (if (arr_i as int) > (arr_i_plus_1 as int) { (arr_i as int) - (arr_i_plus_1 as int) } else { 0 }) + 
                sum_differences(arr@.map_values(|x: i8| x as int), (i + 1) as int));
        }
        sum += diff;
        i += 1;
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
/* code modified by LLM (iteration 5): Fixed lemma call parameter type */
{
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < test_cases.len()
        invariant
            0 <= i <= test_cases.len(),
            results@.len() == i,
            correct_result(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)), 
                         results@.map_values(|x: i8| x as int)),
        decreases test_cases.len() - i,
    {
        proof { lemma_vec_index_valid(&test_cases, i); }
        let test_case = &test_cases[i];
        let sum = calculate_sum_differences(test_case);
        results.push(sum);
        i += 1;
        proof {
            assert(correct_result(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)), 
                               results@.map_values(|x: i8| x as int)));
        }
    }
    results
}
// </vc-code>


}

fn main() {}