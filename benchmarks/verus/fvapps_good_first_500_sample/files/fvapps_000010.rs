// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_subsequence(sub: Seq<i32>, arr: Seq<i32>) -> bool
    decreases sub.len()
{
    if sub.len() == 0 {
        true
    } else {
        exists|i: int| 0 <= i < arr.len() && 
            arr[i] == sub[0] && 
            is_subsequence(sub.skip(1), arr.skip(i + 1))
    }
}

spec fn absolute_diff(a: i32, b: i32) -> int {
    if a >= b { (a - b) as int } else { (b - a) as int }
}

spec fn subsequence_diff_sum(sub: Seq<i32>) -> int
    decreases sub.len()
{
    if sub.len() <= 1 {
        0
    } else {
        absolute_diff(sub[0], sub[1]) + subsequence_diff_sum(sub.skip(1))
    }
}

fn find_max_diff_subsequence(arr: Vec<i32>) -> (result: Vec<i32>)
    requires arr.len() >= 2,
    ensures 
        result.len() >= 2,
        is_subsequence(result@, arr@),
        result[0] == arr[0],
        result[result.len() - 1] == arr[arr.len() - 1],
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}