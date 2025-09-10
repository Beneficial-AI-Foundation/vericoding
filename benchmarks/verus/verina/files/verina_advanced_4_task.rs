/* This task requires writing a Verus method that finds the length of the longest increasing sequence in a given array. The method should return the length of the longest increasing subsequence, in which every element is strictly less than the latter element.

-----Input-----
The input consists of an array:
a: The input array.

-----Output-----
The output is an integer:
Returns the length of the longest increasing subsequence, assuring that it is a subsequence of the input sequence and that every element in it is strictly less than the latter one. */

use vstd::prelude::*;

verus! {
fn int_max(x: i32, y: i32) -> i32 {
    if x < y { y } else { x }
}
fn longest_increasing_subsequence(a: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= a.len(),
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}

fn main() {
    // /*
    // -- Invalid Inputs
    // []
    // -- Tests
    // [
    //     {
    //         "input": {
    //             "a": "#[5, 2, 8, 6, 3, 6, 9, 7]"
    //         },
    //         "expected": 4,
    //         "unexpected": [
    //             2,
    //             3
    //         ]
    //     },
    //     {
    //         "input": {
    //             "a": "#[3, 1, 2, 1, 0]"
    //         },
    //         "expected": 2,
    //         "unexpected": [
    //             1,
    //             3
    //         ]
    //     },
    //     {
    //         "input": {
    //             "a": "#[2, 3, -2, -1, 7, 19, 3, 6, -4, 6, -7, 0, 9, 12, 10]"
    //         },
    //         "expected": 6,
    //         "unexpected": [
    //             5,
    //             3,
    //             10
    //         ]
    //     },
    //     {
    //         "input": {
    //             "a": "#[5, -5, -3, 2, 4, 1, 0, -1, 3, 2, 0]"
    //         },
    //         "expected": 4,
    //         "unexpected": [
    //             2,
    //             5
    //         ]
    //     },
    //     {
    //         "input": {
    //             "a": "#[1, 7, 23, 14, -4, 21, 8, 2, -1, 9, 12, 2]"
    //         },
    //         "expected": 5,
    //         "unexpected": [
    //             2,
    //             4
    //         ]
    //     },
    //     {
    //         "input": {
    //             "a": "#[]"
    //         },
    //         "expected": 0,
    //         "unexpected": [
    //             1,
    //             2
    //         ]
    //     }
    // ]
    // */
}