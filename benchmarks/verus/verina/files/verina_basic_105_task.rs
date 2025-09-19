// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn array_product(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * b[i],
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
                "a": "#[1, 2, 3]",
                "b": "#[4, 5]"
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "a": "#[1, 2, 3]",
                "b": "#[4, 5, 6]"
            },
            "expected": "#[4, 10, 18]",
            "unexpected": [
                "#[4, 10, 17]",
                "#[0, 10, 18]",
                "#[4, 10, 20]"
            ]
        },
        {
            "input": {
                "a": "#[0, 0, 0]",
                "b": "#[1, 2, 3]"
            },
            "expected": "#[0, 0, 0]",
            "unexpected": [
                "#[1, 0, 0]",
                "#[0, 1, 0]",
                "#[0, 0, 1]"
            ]
        },
        {
            "input": {
                "a": "#[-1, 2, -3]",
                "b": "#[3, -4, 5]"
            },
            "expected": "#[-3, -8, -15]",
            "unexpected": [
                "#[-3, -8, -14]",
                "#[-3, -7, -15]",
                "#[-2, -8, -15]"
            ]
        },
        {
            "input": {
                "a": "#[2]",
                "b": "#[10]"
            },
            "expected": "#[20]",
            "unexpected": [
                "#[10]",
                "#[0]",
                "#[30]"
            ]
        },
        {
            "input": {
                "a": "#[1, 2, 3, 4]",
                "b": "#[2, 2, 2, 2]"
            },
            "expected": "#[2, 4, 6, 8]",
            "unexpected": [
                "#[2, 4, 6, 9]",
                "#[1, 4, 6, 8]",
                "#[2, 5, 6, 8]"
            ]
        }
    ]
    */
}