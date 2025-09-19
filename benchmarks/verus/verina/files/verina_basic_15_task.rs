// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| {
            &&& 0 <= i < a.len() - 1
            &&& #[trigger] a[i] + 1 == a[(i + 1) as int]
        },
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
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
                "a": "#[1, 2, 3, 5]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "a": "#[1, 3, 5, 7]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "a": "#[]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "a": "#[10]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "a": "#[5, 6]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "a": "#[5, 7, 8, 10]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "a": "#[9, 9, 10]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "a": "#[3, 3, 3]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        }
    ]
    */
}