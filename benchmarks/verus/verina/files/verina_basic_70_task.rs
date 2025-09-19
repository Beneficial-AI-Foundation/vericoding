// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn linear_search3(a: &Vec<i32>, p: spec_fn(i32) -> bool) -> (result: usize)
    requires 
        exists|i: int| 0 <= i < a.len() && p(a[i]),
    ensures 
        result < a.len(),
        p(a[result as int]),
        forall|k: int| 0 <= k < result ==> !p(a[k]),
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
    [
        {
            "input": {
                "a": "#[1, 2, 3, 4, 5]",
                "P": "fun x => x > 10"
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "a": "#[4, 7, 2, 9]",
                "P": "fun x => x > 5"
            },
            "expected": 1,
            "unexpected": [
                0,
                2,
                3
            ]
        },
        {
            "input": {
                "a": "#[10, 8, 6, 4, 2]",
                "P": "fun x => x < 5"
            },
            "expected": 3,
            "unexpected": [
                0,
                1,
                4
            ]
        },
        {
            "input": {
                "a": "#[5, 3, 1, 2]",
                "P": "fun x => x == 1"
            },
            "expected": 2,
            "unexpected": [
                0,
                1,
                3
            ]
        },
        {
            "input": {
                "a": "#[0, 1, 2, 3]",
                "P": "fun x => x == 0"
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
                "a": "#[9, 9, 9, 9]",
                "P": "fun x => x == 9"
            },
            "expected": 0,
            "unexpected": [
                1,
                2,
                3
            ]
        }
    ]
    */
}