// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
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
                "x": 0
            },
            "expected": 0,
            "unexpected": [
                1,
                -1,
                10
            ]
        },
        {
            "input": {
                "x": 1
            },
            "expected": 3,
            "unexpected": [
                2,
                4,
                0
            ]
        },
        {
            "input": {
                "x": -2
            },
            "expected": -6,
            "unexpected": [
                -4,
                -2,
                6
            ]
        },
        {
            "input": {
                "x": 10
            },
            "expected": 30,
            "unexpected": [
                20,
                40,
                0
            ]
        },
        {
            "input": {
                "x": -5
            },
            "expected": -15,
            "unexpected": [
                -10,
                -5,
                15
            ]
        }
    ]
    */
}