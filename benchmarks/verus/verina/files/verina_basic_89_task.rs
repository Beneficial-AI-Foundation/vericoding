// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn set_to_seq(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        // All elements are unique in the result  
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
        // Every element in result is in s
        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < s.len() && s[j] == #[trigger] result[i],
        // Every element in s is in result
        forall|i: int| 0 <= i < s.len() ==> 
            exists|j: int| 0 <= j < result.len() && result[j] == #[trigger] s[i],
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
                "s": "[1, 2, 2, 3, 1]"
            },
            "expected": "[1, 2, 3]",
            "unexpected": [
                "[1, 3, 2]",
                "[1, 2, 2, 3]",
                "[2, 1, 3]"
            ]
        },
        {
            "input": {
                "s": "[5, 5, 5, 5]"
            },
            "expected": "[5]",
            "unexpected": [
                "[5, 5]",
                "[]",
                "[6]"
            ]
        },
        {
            "input": {
                "s": "[]"
            },
            "expected": "[]",
            "unexpected": [
                "[1]",
                "[2]",
                "[0]"
            ]
        },
        {
            "input": {
                "s": "[11, 22, 33]"
            },
            "expected": "[11, 22, 33]",
            "unexpected": [
                "[33, 22, 11]",
                "[11, 11, 22, 33]",
                "[11, 33]"
            ]
        },
        {
            "input": {
                "s": "[3, 1, 4, 1, 5, 9, 2, 6, 5]"
            },
            "expected": "[3, 1, 4, 5, 9, 2, 6]",
            "unexpected": [
                "[3, 1, 4, 1, 5, 9, 2, 6, 5]",
                "[1, 3, 4, 5, 9, 2, 6]",
                "[3, 1, 4, 5, 9, 6]"
            ]
        }
    ]
    */
}