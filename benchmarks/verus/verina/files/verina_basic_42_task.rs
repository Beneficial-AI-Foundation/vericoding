// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_digit(c: char) -> bool {
    '0' <= c && c <= '9'
}
// </vc-helpers>

// <vc-spec>
fn count_digits(s: &str) -> (result: usize)
    ensures
        result >= 0,
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
                "s": "123abc456"
            },
            "expected": 6,
            "unexpected": [
                5,
                7,
                0
            ]
        },
        {
            "input": {
                "s": "no digits here!"
            },
            "expected": 0,
            "unexpected": [
                1,
                2,
                3
            ]
        },
        {
            "input": {
                "s": "1234567890"
            },
            "expected": 10,
            "unexpected": [
                9,
                11,
                0
            ]
        },
        {
            "input": {
                "s": ""
            },
            "expected": 0,
            "unexpected": [
                1,
                2,
                10
            ]
        },
        {
            "input": {
                "s": "a1b2c3"
            },
            "expected": 3,
            "unexpected": [
                2,
                4,
                5
            ]
        },
        {
            "input": {
                "s": "0"
            },
            "expected": 1,
            "unexpected": [
                0,
                2,
                10
            ]
        },
        {
            "input": {
                "s": "abc"
            },
            "expected": 0,
            "unexpected": [
                1,
                8,
                9
            ]
        }
    ]
    */
}