// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    ensures
        result <= a.len(),
        result == a.len() || a[result as int] == e,
        forall|i: int| 0 <= i < result ==> a[i] != e,
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
                "a": "#[1, 3, 5, 7, 9]",
                "e": 5
            },
            "expected": "2",
            "unexpected": [
                "1",
                "3",
                "4"
            ]
        },
        {
            "input": {
                "a": "#[2, 4, 6, 8]",
                "e": 5
            },
            "expected": "4",
            "unexpected": [
                "1",
                "3",
                "5"
            ]
        },
        {
            "input": {
                "a": "#[5, 5, 5]",
                "e": 5
            },
            "expected": "0",
            "unexpected": [
                "1",
                "2",
                "3"
            ]
        },
        {
            "input": {
                "a": "#[10, 9, 8, 7]",
                "e": 10
            },
            "expected": "0",
            "unexpected": [
                "1",
                "2",
                "3"
            ]
        },
        {
            "input": {
                "a": "#[1, 2, 3, 3, 4]",
                "e": 3
            },
            "expected": "2",
            "unexpected": [
                "1",
                "3",
                "4"
            ]
        }
    ]
    */
}