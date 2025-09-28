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
/* helper modified by LLM (iteration 5): Use exec access for comparisons to fix compilation error with spec types in exec code */
fn get_sum(arr: &Vec<i8>) -> (sum: i8)
 requires
  1 <= arr.len(),
 ensures
  sum as int == sum_differences(arr@.map_values(|x: i8| x as int), 0),
{
 let mut sum: i8 = 0;
 let arr_len: usize = arr.len();
 let mut i: usize = 0;
 while i < arr_len - 1
  invariant
   0 <= (i as int) <= (arr_len as int) - 1,
   sum as int == sum_differences(arr@.map_values(|x: i8| x as int), i as int),
  decreases (arr_len as int) - 1 - (i as int)
 {
  if arr[i] > arr[i + 1] {
   sum = sum + (arr[i] - arr[i + 1]);
  }
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
/* code modified by LLM (iteration 5): Compute sum for each test case using helper function */
{
    let mut results = Vec::new();
    for tc in test_cases {
        let sum = get_sum(&tc);
        results.push(sum);
    }
    results
}
// </vc-code>


}

fn main() {}