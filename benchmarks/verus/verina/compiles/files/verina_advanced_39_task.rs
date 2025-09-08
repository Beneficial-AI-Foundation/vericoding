/* This task requires writing a Verus function that returns the maximum element from a non-empty list of natural numbers.

Input: The input consists of lst: a non-empty list of natural numbers.

Output: The output is a natural number representing the largest element in the list. */

use vstd::prelude::*;

verus! {
fn max_of_list(lst: &Vec<usize>) -> (result: usize)
    requires lst.len() > 0,
    ensures
        exists|i: int| 0 <= i < lst.len() && lst[i] == result,
        forall|i: int| 0 <= i < lst.len() ==> lst[i] <= result,
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {
    /* 
    -- Invalid Inputs
    [
        {
            "input": {
                "lst": "[]"
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "lst": "[1, 2, 3]"
            },
            "expected": 3,
            "unexpected": [
                2,
                1,
                0
            ]
        },
        {
            "input": {
                "lst": "[5, 5, 5]"
            },
            "expected": 5,
            "unexpected": [
                4,
                0
            ]
        },
        {
            "input": {
                "lst": "[10, 1, 9]"
            },
            "expected": 10,
            "unexpected": [
                1,
                9
            ]
        },
        {
            "input": {
                "lst": "[7]"
            },
            "expected": 7,
            "unexpected": [
                0,
                6
            ]
        },
        {
            "input": {
                "lst": "[0, 0, 0, 0]"
            },
            "expected": 0,
            "unexpected": [
                1
            ]
        }
    ]
    */
}