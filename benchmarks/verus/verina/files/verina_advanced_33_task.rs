// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: Vec<i32>) -> (result: usize)
    ensures
        result >= 0,
        nums.len() == 0 ==> result == 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {
    /* 
    -- Invalid Inputs
    []
    -- Tests
    [
        {
            "input": {
                "nums": "[10, 9, 2, 5, 3, 7, 101, 18]"
            },
            "expected": 4,
            "unexpected": [
                3,
                5
            ]
        },
        {
            "input": {
                "nums": "[0, 1, 0, 3, 2, 3]"
            },
            "expected": 4,
            "unexpected": [
                3
            ]
        },
        {
            "input": {
                "nums": "[7, 7, 7, 7, 7]"
            },
            "expected": 1,
            "unexpected": [
                0,
                2
            ]
        },
        {
            "input": {
                "nums": "[]"
            },
            "expected": 0,
            "unexpected": [
                1
            ]
        },
        {
            "input": {
                "nums": "[4, 10, 4, 3, 8, 9]"
            },
            "expected": 3,
            "unexpected": [
                2,
                4
            ]
        }
    ]
    */
}