// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result >= a && result >= b && result >= c,
        result == a || result == b || result == c,
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
                "a": 3,
                "b": 2,
                "c": 1
            },
            "expected": 3,
            "unexpected": [
                2,
                1,
                -1
            ]
        },
        {
            "input": {
                "a": 5,
                "b": 5,
                "c": 5
            },
            "expected": 5,
            "unexpected": [
                6,
                4
            ]
        },
        {
            "input": {
                "a": 10,
                "b": 20,
                "c": 15
            },
            "expected": 20,
            "unexpected": [
                10,
                15
            ]
        },
        {
            "input": {
                "a": -1,
                "b": -2,
                "c": -3
            },
            "expected": -1,
            "unexpected": [
                -2,
                -3
            ]
        },
        {
            "input": {
                "a": 0,
                "b": -10,
                "c": -5
            },
            "expected": 0,
            "unexpected": [
                -5,
                -10
            ]
        }
    ]
    */
}