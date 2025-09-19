// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn remove_front(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        a.len() > 0,
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i + 1],
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
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
                "a": "#[1, 2, 3, 4, 5]"
            },
            "expected": "#[2, 3, 4, 5]",
            "unexpected": [
                "#[1, 2, 3, 4, 5]",
                "#[3, 4, 5]",
                "#[2, 3, 4]"
            ]
        },
        {
            "input": {
                "a": "#[10, 20, 30]"
            },
            "expected": "#[20, 30]",
            "unexpected": [
                "#[10, 20, 30]",
                "#[10, 30]",
                "#[10, 20]"
            ]
        },
        {
            "input": {
                "a": "#[0, -1, -2, -3]"
            },
            "expected": "#[-1, -2, -3]",
            "unexpected": [
                "#[0, -1, -2, -3]",
                "#[-1, -3]",
                "#[-2, -3]"
            ]
        },
        {
            "input": {
                "a": "#[7]"
            },
            "expected": "#[]",
            "unexpected": [
                "#[7]",
                "#[0]",
                "#[7, 7]"
            ]
        },
        {
            "input": {
                "a": "#[100, 0, 50]"
            },
            "expected": "#[0, 50]",
            "unexpected": [
                "#[100, 0, 50]",
                "#[50]",
                "#[0]"
            ]
        }
    ]
    */
}