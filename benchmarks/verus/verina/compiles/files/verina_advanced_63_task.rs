/* This task requires writing a Verus method that counts the unique elements from a sorted array.

-----Input-----
The input is a single list of integers:
nums: An array of integers sorted in non-decreasing order.

-----Output-----
The output is a single integer:
Returns the number of unique elements (k). */

use vstd::prelude::*;

verus! {
fn remove_duplicates(nums: &Vec<i32>) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
    ensures result <= nums.len(),
{
    // impl-start
    assume(false);
    0
    // impl-end
}

proof fn remove_duplicates_spec_satisfied(nums: &Vec<i32>)
    requires forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
{
    assume(false); // TODO: Remove this line and implement the proof
}
}
fn main() {
    /* 
    -- Invalid Inputs
    [
        {
            "input": {
                "nums": "[3, 2, 1]"
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "nums": "[1, 1, 2]"
            },
            "expected": 2,
            "unexpected": [
                1,
                3
            ]
        },
        {
            "input": {
                "nums": "[0, 0, 1, 1, 1, 2, 2, 3, 3, 4]"
            },
            "expected": 5,
            "unexpected": [
                4,
                10
            ]
        },
        {
            "input": {
                "nums": "[-1, -1, 0, 1, 2, 2, 3]"
            },
            "expected": 5,
            "unexpected": [
                3
            ]
        },
        {
            "input": {
                "nums": "[1, 2, 3, 4, 5]"
            },
            "expected": 5,
            "unexpected": [
                4
            ]
        },
        {
            "input": {
                "nums": "[1, 1, 1, 1]"
            },
            "expected": 1,
            "unexpected": [
                2,
                4
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
                "nums": "[1]"
            },
            "expected": 1,
            "unexpected": [
                0,
                2
            ]
        },
        {
            "input": {
                "nums": "[-100, -100, -100]"
            },
            "expected": 1,
            "unexpected": [
                2,
                3
            ]
        },
        {
            "input": {
                "nums": "[-100, -99, -99, -50, 0, 0, 100, 100]"
            },
            "expected": 5,
            "unexpected": [
                6,
                7
            ]
        },
        {
            "input": {
                "nums": "[-1, 0, 0, 0, 1, 2, 2, 3, 4, 4, 5]"
            },
            "expected": 7,
            "unexpected": [
                6,
                10
            ]
        },
        {
            "input": {
                "nums": "[100, 100, 100, 101, 102, 102, 103, 104, 105, 105]"
            },
            "expected": 6,
            "unexpected": [
                5,
                7
            ]
        }
    ]
    */
}