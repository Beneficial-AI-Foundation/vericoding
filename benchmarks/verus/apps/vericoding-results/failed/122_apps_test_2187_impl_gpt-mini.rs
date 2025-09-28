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
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> */
spec fn vec_to_seq(v: Vec<i8>) -> Seq<int> {
    v@.map_values(|x: i8| x as int)
}

/* helper modified by LLM (iteration 5): prove sum_differences is nonnegative for all starts */
proof fn sum_differences_nonneg_start(s: Seq<int>, start: int)
    ensures
        sum_differences(s, start) >= 0,
    decreases s.len() - start
{
    if start >= s.len() - 1 {
        proof { assert(sum_differences(s, start) == 0); }
    } else {
        let term = if s[start] > s[start + 1] { s[start] - s[start + 1] } else { 0 };
        assert(term >= 0);
        sum_differences_nonneg_start(s, start + 1);
        proof { assert(sum_differences(s, start) == term + sum_differences(s, start + 1)); }
    }
}

/* helper modified by LLM (iteration 5): wrapper over sequence lemma for Vec<i8> */
proof fn sum_differences_nonneg(v: Vec<i8>)
    ensures
        sum_differences(vec_to_seq(v), 0) >= 0,
    decreases v@.len()
{
    sum_differences_nonneg_start(vec_to_seq(v), 0);
}

// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<Vec<i8>>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)))
    ensures correct_result(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)), results@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implement solve using indexing to avoid Option types */
{
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < test_cases.len() {
        let tc: Vec<i8> = test_cases[i].clone();
        let mut sum: i32 = 0;
        let mut j: usize = 0;
        while j + 1 < tc.len() {
            let a: i8 = tc[j];
            let b: i8 = tc[j + 1];
            if (a as i32) > (b as i32) {
                sum = sum + ((a as i32) - (b as i32));
            }
            j = j + 1;
        }
        results.push(sum as i8);
        i = i + 1;
    }
    results
}

// </vc-code>


}

fn main() {}