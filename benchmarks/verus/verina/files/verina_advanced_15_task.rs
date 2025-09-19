// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn increasing_triplet(nums: &Vec<i32>) -> (result: bool)
    ensures
        result ==> exists|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k],
        !result ==> forall|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k]),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
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
                "nums": "[1, 2, 3]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "nums": "[5, 4, 3, 2, 1]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "nums": "[2, 1, 5, 0, 4, 6]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "nums": "[1, 5, 0, 4, 1, 3]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "nums": "[5, 4, 3]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "nums": "[]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        }
    ]
    */
}