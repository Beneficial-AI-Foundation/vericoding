/* This task involves computing the element-wise product of two integer arrays. For each position in the arrays, the corresponding numbers are multiplied together. If an element is missing in one of the arrays at a given index, the missing value is treated as 0. When both arrays provide values for every index, the resulting array will contain the product of the two numbers at each corresponding index.

-----Input-----
The input consists of two arrays:
• a: An array of integers.
• b: An array of integers (should be of equal length to a for the specification to hold).

-----Output-----
The output is an array of integers that:
• Has the same length as the input arrays.
• For each index i, the output array contains the product a[i] * b[i].
• In cases where one of the arrays might be shorter, missing elements default to 0 during multiplication.

-----Note-----
It is assumed that the arrays are of equal length for the theorem specification, although the implementation defaults missing indices to 0. */

use vstd::prelude::*;

verus! {
fn array_product(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * b[i],
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
                "a": "#[1, 2, 3]",
                "b": "#[4, 5]"
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "a": "#[1, 2, 3]",
                "b": "#[4, 5, 6]"
            },
            "expected": "#[4, 10, 18]",
            "unexpected": [
                "#[4, 10, 17]",
                "#[0, 10, 18]",
                "#[4, 10, 20]"
            ]
        },
        {
            "input": {
                "a": "#[0, 0, 0]",
                "b": "#[1, 2, 3]"
            },
            "expected": "#[0, 0, 0]",
            "unexpected": [
                "#[1, 0, 0]",
                "#[0, 1, 0]",
                "#[0, 0, 1]"
            ]
        },
        {
            "input": {
                "a": "#[-1, 2, -3]",
                "b": "#[3, -4, 5]"
            },
            "expected": "#[-3, -8, -15]",
            "unexpected": [
                "#[-3, -8, -14]",
                "#[-3, -7, -15]",
                "#[-2, -8, -15]"
            ]
        },
        {
            "input": {
                "a": "#[2]",
                "b": "#[10]"
            },
            "expected": "#[20]",
            "unexpected": [
                "#[10]",
                "#[0]",
                "#[30]"
            ]
        },
        {
            "input": {
                "a": "#[1, 2, 3, 4]",
                "b": "#[2, 2, 2, 2]"
            },
            "expected": "#[2, 4, 6, 8]",
            "unexpected": [
                "#[2, 4, 6, 9]",
                "#[1, 4, 6, 8]",
                "#[2, 5, 6, 8]"
            ]
        }
    ]
    */
}