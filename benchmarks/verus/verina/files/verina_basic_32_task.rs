// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap_first_and_last(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        result.len() == a.len(),
        result[0] == a[a.len() - 1],
        result[result.len() - 1] == a[0],
        forall|i: int| 1 <= i < result.len() - 1 ==> result[i] == a[i],
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
    Invalid Inputs
    [
        {
            "input": {
                "a": "[]"
            }
        }
    ]
    Tests
    [
        {
            "input": {
                "a": "[1, 2, 3, 4, 5]"
            },
            "expected": "[5, 2, 3, 4, 1]",
            "unexpected": [
                "[1, 2, 3, 4, 5]",
                "[5, 4, 3, 2, 1]",
                "[2, 3, 4, 5, 1]"
            ]
        },
        {
            "input": {
                "a": "[10]"
            },
            "expected": "[10]",
            "unexpected": [
                "[0]",
                "[5]",
                "[11]"
            ]
        },
        {
            "input": {
                "a": "[1, 2]"
            },
            "expected": "[2, 1]",
            "unexpected": [
                "[1, 2]",
                "[2, 2]",
                "[1, 1]"
            ]
        },
        {
            "input": {
                "a": "[1, 2, 3]"
            },
            "expected": "[3, 2, 1]",
            "unexpected": [
                "[1, 2, 3]",
                "[3, 1, 2]",
                "[2, 1, 3]"
            ]
        }
    ]
    */
}