// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn test_array_elements(a: &Vec<i32>, j: usize) -> (result: Vec<i32>)
    requires j < a.len(),
    ensures
        result.len() == a.len(),
        result[j as int] == 60,
        forall|k: int| 0 <= k < a.len() && k != j ==> result[k] == a[k],
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
                "a": "#[1, 2, 3, 4]",
                "j": 5
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "a": "#[1, 2, 3, 4, 5]",
                "j": 2
            },
            "expected": "#[1, 2, 60, 4, 5]",
            "unexpected": [
                "#[1, 2, 3, 4, 5]",
                "#[1, 60, 3, 4, 5]"
            ]
        },
        {
            "input": {
                "a": "#[60, 30, 20]",
                "j": 1
            },
            "expected": "#[60, 60, 20]",
            "unexpected": [
                "#[60, 30, 20]",
                "#[60, 30, 60]"
            ]
        },
        {
            "input": {
                "a": "#[10, 20, 30]",
                "j": 0
            },
            "expected": "#[60, 20, 30]",
            "unexpected": [
                "#[10, 20, 30]",
                "#[10, 60, 30]"
            ]
        },
        {
            "input": {
                "a": "#[5, 10, 15]",
                "j": 2
            },
            "expected": "#[5, 10, 60]",
            "unexpected": [
                "#[5, 10, 15]",
                "#[5, 60, 15]"
            ]
        },
        {
            "input": {
                "a": "#[0]",
                "j": 0
            },
            "expected": "#[60]",
            "unexpected": [
                "#[0]",
                "#[70]"
            ]
        }
    ]
    */
}