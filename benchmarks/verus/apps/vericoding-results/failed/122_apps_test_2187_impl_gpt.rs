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
proof fn sum_differences_nonnegative(arr: Seq<int>, start: int)
    requires
        0 <= start <= arr.len(),
    ensures
        sum_differences(arr, start) >= 0,
{
    if start >= arr.len() - 1 {
        // sum_differences(arr, start) == 0 by definition
    } else {
        let d = if arr[start] > arr[start + 1] { arr[start] - arr[start + 1] } else { 0 };
        sum_differences_nonnegative(arr, start + 1);
        assert(d >= 0);
    }
}

fn compute_sum_diffs_i8(v: &Vec<i8>) -> (s: int)
    ensures
        s == sum_differences(v@.map_values(|x: i8| x as int), 0),
        s >= 0,
{
    let n = v.len();
    let arr_s = v@.map_values(|x: i8| x as int);
    let mut i: usize = 0;
    let mut acc: int = 0;
    while i + 1 < n
        invariant
            i <= n,
            acc + sum_differences(arr_s, i as int) == sum_differences(arr_s, 0),
            acc >= 0,
        decreases n - i
    {
        let ai: int = v[i] as int;
        let aj: int = v[i + 1] as int;
        let d: int = if ai > aj { ai - aj } else { 0 };
        proof {
            assert(sum_differences(arr_s, i as int) == d + sum_differences(arr_s, i as int + 1));
        }
        acc = acc + d;
        i = i + 1;
    }
    proof {
        if i + 1 >= n {
            assert(i >= n - 1);
            assert(sum_differences(arr_s, i as int) == 0);
        }
        sum_differences_nonnegative(arr_s, 0);
    }
    acc
}
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<Vec<i8>>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)))
    ensures correct_result(test_cases@.map_values(|v: Vec<i8>| v@.map_values(|x: i8| x as int)), results@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    let tc_len = test_cases.len();
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < tc_len
        invariant
            i <= tc_len,
            results@.len() == i,
            forall|k: int| 0 <= k < results@.len() ==> (results@[k] as int) >= 0,
        decreases tc_len - i
    {
        let ref v = test_cases[i];
        let s: int = compute_sum_diffs_i8(v);
        let r: i8 = if s <= 127 { s as i8 } else { 127i8 };
        results.push(r);
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}