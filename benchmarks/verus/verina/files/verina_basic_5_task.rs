// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
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
                "b": 4
            },
            "expected": 12,
            "unexpected": [
                0,
                11,
                15
            ]
        },
        {
            "input": {
                "a": 3,
                "b": -4
            },
            "expected": -12,
            "unexpected": [
                0,
                -11,
                12
            ]
        },
        {
            "input": {
                "a": -3,
                "b": 4
            },
            "expected": -12,
            "unexpected": [
                0,
                -11,
                12
            ]
        },
        {
            "input": {
                "a": -3,
                "b": -4
            },
            "expected": 12,
            "unexpected": [
                0,
                11,
                -12
            ]
        },
        {
            "input": {
                "a": 0,
                "b": 5
            },
            "expected": 0,
            "unexpected": [
                1,
                -1,
                5
            ]
        },
        {
            "input": {
                "a": 5,
                "b": 0
            },
            "expected": 0,
            "unexpected": [
                1,
                -1,
                5
            ]
        },
        {
            "input": {
                "a": 0,
                "b": 0
            },
            "expected": 0,
            "unexpected": [
                1,
                -1,
                5
            ]
        }
    ]
    */
}