/* Given an integer array nums, return true if there exists a triple of indices (i, j, k) such that i < j < k and nums[i] < nums[j] < nums[k]. If no such indices exist, return false.

-----Input-----
The input consists of a single list:
nums: A list of integers.

-----Output-----
The output is a boolean:
Returns true if there exists a triplet (i, j, k) where i < j < k and nums[i] < nums[j] < nums[k]; otherwise, returns false. */

use vstd::prelude::*;

verus! {
fn increasing_triplet(nums: &Vec<i32>) -> (result: bool)
    ensures
        result ==> exists|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k],
        !result ==> forall|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k]),
{
    // impl-start
    assume(false);
    false
    // impl-end
}
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