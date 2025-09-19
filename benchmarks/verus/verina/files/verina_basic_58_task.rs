// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
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
    []
    -- Tests
    [
        {
            "input": {
                "s": "#[]"
            },
            "expected": "#[]",
            "unexpected": [
                "#[1]",
                "#[0]",
                "#[-1]"
            ]
        },
        {
            "input": {
                "s": "#[1, 2, 3, 4, 5]"
            },
            "expected": "#[2, 4, 6, 8, 10]",
            "unexpected": [
                "#[1, 2, 3, 4, 5]",
                "#[2, 4, 6, 8, 9]",
                "#[0, 4, 6, 8, 10]"
            ]
        },
        {
            "input": {
                "s": "#[0, -1, 5]"
            },
            "expected": "#[0, -2, 10]",
            "unexpected": [
                "#[0, -1, 5]",
                "#[1, -2, 10]",
                "#[0, 0, 10]"
            ]
        },
        {
            "input": {
                "s": "#[100]"
            },
            "expected": "#[200]",
            "unexpected": [
                "#[100]",
                "#[0]",
                "#[201]"
            ]
        },
        {
            "input": {
                "s": "#[-3, -4]"
            },
            "expected": "#[-6, -8]",
            "unexpected": [
                "#[3, -4]",
                "#[-6, -7]",
                "#[-6, -9]"
            ]
        }
    ]
    */
}