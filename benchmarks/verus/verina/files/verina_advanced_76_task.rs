// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn top_k_frequent(nums: &Vec<i32>, k: usize) -> (result: Vec<i32>)
    requires 
        k <= nums@.to_set().len(),
    ensures
        result.len() == k,
        forall|x: i32| result@.contains(x) ==> nums@.contains(x),
        result@.no_duplicates(),
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
                "nums": "[1, 2, 3]",
                "k": 4
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "nums": "[1, 1, 1, 2, 2, 3]",
                "k": 2
            },
            "expected": "[1, 2]",
            "unexpected": [
                "[1, 3]",
                "[2, 3]"
            ]
        },
        {
            "input": {
                "nums": "[4, 1, -1, 2, -1, 2, 3]",
                "k": 2
            },
            "expected": "[-1, 2]",
            "unexpected": [
                "[-1, 4]",
                "[4, 3]"
            ]
        },
        {
            "input": {
                "nums": "[5]",
                "k": 1
            },
            "expected": "[5]",
            "unexpected": [
                "[]"
            ]
        },
        {
            "input": {
                "nums": "[7, 7, 7, 8, 8, 9]",
                "k": 1
            },
            "expected": "[7]",
            "unexpected": [
                "[8]"
            ]
        },
        {
            "input": {
                "nums": "[]",
                "k": 0
            },
            "expected": "[]",
            "unexpected": [
                "[0]"
            ]
        }
    ]
    */
}