/* This task is about processing an array of integers by producing a new array that excludes the first element. The objective is to define a clear behavior: if the array contains at least one element, return a modified array starting from the second element.

-----Input-----
The input consists of:
• a: An array of integers.

-----Output-----
The output is an array of integers that:
• Has a length equal to the original array's length minus one.
• Contains the same elements as the input array except for the first element.
• Satisfies the condition that for every index i in the output array, the element at position i is equal to the element at position i+1 in the input array.

-----Note-----
It is assumed that the input array is non-empty. */

use vstd::prelude::*;

verus! {
fn remove_front(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        a.len() > 0,
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i + 1],
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {
    /* 
    -- Invalid Inputs
    [
        {
            "input": {
                "a": "#[]"
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "a": "#[1, 2, 3, 4, 5]"
            },
            "expected": "#[2, 3, 4, 5]",
            "unexpected": [
                "#[1, 2, 3, 4, 5]",
                "#[3, 4, 5]",
                "#[2, 3, 4]"
            ]
        },
        {
            "input": {
                "a": "#[10, 20, 30]"
            },
            "expected": "#[20, 30]",
            "unexpected": [
                "#[10, 20, 30]",
                "#[10, 30]",
                "#[10, 20]"
            ]
        },
        {
            "input": {
                "a": "#[0, -1, -2, -3]"
            },
            "expected": "#[-1, -2, -3]",
            "unexpected": [
                "#[0, -1, -2, -3]",
                "#[-1, -3]",
                "#[-2, -3]"
            ]
        },
        {
            "input": {
                "a": "#[7]"
            },
            "expected": "#[]",
            "unexpected": [
                "#[7]",
                "#[0]",
                "#[7, 7]"
            ]
        },
        {
            "input": {
                "a": "#[100, 0, 50]"
            },
            "expected": "#[0, 50]",
            "unexpected": [
                "#[100, 0, 50]",
                "#[50]",
                "#[0]"
            ]
        }
    ]
    */
}