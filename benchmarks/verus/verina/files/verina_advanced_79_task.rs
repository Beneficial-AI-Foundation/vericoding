// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn two_sum(nums: Vec<i32>, target: i32) -> (result: Option<(usize, usize)>)
    ensures
        match result {
            None => {
                forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j ==> nums[i] + nums[j] != target
            },
            Some((i, j)) => {
                i < j &&
                j < nums.len() &&
                nums[i as int] + nums[j as int] == target &&
                forall|k1: int, k2: int| 0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 < k2 && (k1 < i || (k1 == i && k2 < j)) ==> nums[k1] + nums[k2] != target
            }
        },
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    None
    // impl-end
}
// </vc-code>


}
fn main() {
    /*
    -- Tests
    [
        {
            "input": {
                "nums": "[2, 7, 11, 15]",
                "target": 9
            },
            "expected": "some (0, 1)",
            "unexpected": [
                "some (1, 2)",
                "none"
            ]
        },
        {
            "input": {
                "nums": "[3, 2, 4]",
                "target": 6
            },
            "expected": "some (1, 2)",
            "unexpected": [
                "some (0, 2)",
                "none"
            ]
        },
        {
            "input": {
                "nums": "[3, 3]",
                "target": 6
            },
            "expected": "some (0, 1)",
            "unexpected": [
                "some (1, 1)",
                "none"
            ]
        },
        {
            "input": {
                "nums": "[1, 2, 3]",
                "target": 7
            },
            "expected": "none",
            "unexpected": [
                "some (0, 2)"
            ]
        },
        {
            "input": {
                "nums": "[0, 4, 3, 0]",
                "target": 0
            },
            "expected": "some (0, 3)",
            "unexpected": [
                "some (1, 2)",
                "none"
            ]
        }
    ]
    */
}