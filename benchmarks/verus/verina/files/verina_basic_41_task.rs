// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn has_only_one_distinct_element(a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0,
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]),
        !result ==> (exists|i: int| 0 <= i < a.len() && #[trigger] a[i] != a[0]),
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
                "a": "#[1, 1, 1]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "a": "#[1, 2, 1]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "a": "#[3, 4, 5, 6]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "a": "#[7]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "a": "#[0, 0, 0, 0]"
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "a": "#[0, 0, 1, 0]"
            },
            "expected": false,
            "unexpected": [
                true
            ]
        }
    ]
    */
}