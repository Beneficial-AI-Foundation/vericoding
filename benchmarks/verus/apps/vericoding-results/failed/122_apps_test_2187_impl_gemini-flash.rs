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
/* helper modified by LLM (iteration 5): removed helper function as it was no longer needed */
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<Vec<i8>>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)))
    ensures correct_result(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)), results@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Cast `i8` values to `int` within the `map_values` closure to fix compilation error. */
{
    let mut results: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < test_cases.len()
        invariant
            0 <= i <= test_cases.len(),
            results.len() == i,
            // All accumulated results are correct for the processed test cases
            forall|j: int| 0 <= j < i ==> {
                let current_test_case_seq_inv = test_cases@[j].map_values(|x: i8| x as int);
                let current_result_int = results@[j] as int;
                current_result_int == sum_differences(current_test_case_seq_inv, 0)
            },
            // All accumulated results are non-negative
            forall|j: int| 0 <= j < i ==> results@[j] >= 0
        decreases test_cases.len() - i
    {
        let mut current_sum_diff: i8 = 0;
        let current_test_case = &test_cases[i];
        // The `current_test_case_seq` is only used in invariant. It can remain `Seq<int>`.
        let current_test_case_seq = current_test_case@.map_values(|x: i8| x as int);
        
        if current_test_case.len() >= 2 {
            let mut j = 0;
            while j < current_test_case.len() - 1
                invariant
                    0 <= j <= current_test_case.len() - 1,
                    // The ghost `sum_differences` is defined over `Seq<int>`, so we need to map `i8` to `int` for verification
                    (current_sum_diff as int) == sum_differences(current_test_case_seq.subsequence(j as nat, current_test_case_seq.len()), 0),
                    current_sum_diff >= 0
                decreases current_test_case.len() - 1 - j
            {
                if current_test_case[j] > current_test_case[j + 1] {
                    // Perform operations in `i8` type.
                    current_sum_diff = current_sum_diff + (current_test_case[j] - current_test_case[j + 1]);
                }
                j = j + 1;
            }
        }

        results.push(current_sum_diff);
        i = i + 1;
    }

    results
}
// </vc-code>


}

fn main() {}