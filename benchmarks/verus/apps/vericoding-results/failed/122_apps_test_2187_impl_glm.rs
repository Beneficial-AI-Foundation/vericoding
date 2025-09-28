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
/* helper modified by LLM (iteration 5): fixed compilation errors by using i64 for arithmetic and ghost variable for invariant */
fn compute_sum_differences(arr: &Vec<i8>) -> (sum: i8)
    requires arr.len() >= 1,
    ensures sum as int == sum_differences(arr@.map_values(|x: i8| x as int), 0)
{
    let mut total_exec: i64 = 0;
    let mut i = 0;
    ghost var total_ghost: int = 0;

    while i+1 < arr.len()
        invariant
            i <= arr.len() - 1,
            total_ghost == sum_differences(arr@.map_values(|x| x as int), 0) - sum_differences(arr@.map_values(|x| x as int), i as int),
            total_exec == total_ghost as i64,
        decreases (arr.len() - i)
    {
        let a = arr[i] as i64;
        let b = arr[i+1] as i64;
        if a > b {
            let diff = a - b;
            total_exec = total_exec + diff;
        }
        proof {
            let term = if arr@[i] as int > arr@[i+1] as int {
                (arr@[i] as int) - (arr@[i+1] as int)
            } else {
                0
            };
            total_ghost = total_ghost + term;
        }
        i = i + 1;
    }

    let result = total_exec as i8;
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<Vec<i8>>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)))
    ensures correct_result(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)), results@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed by updating the helper function */
{
    let mut results = Vec::new();
    for i in 0..test_cases.len() {
        let arr = &test_cases[i];
        let sum = compute_sum_differences(arr);
        results.push(sum);
    }
    results
}
// </vc-code>


}

fn main() {}