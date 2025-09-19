// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn search_insert(xs: &Vec<i32>, target: i32) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j],
    ensures
        result <= xs.len(),
        forall|i: int| 0 <= i < result ==> xs[i] < target,
        result < xs.len() ==> target <= xs[result as int],
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
    /* Invalid Inputs
    [
        {
            "input": {
                "xs": "[2, 1]",
                "target": 5
            }
        },
        {
            "input": {
                "xs": "[1, 1]",
                "target": 2
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "xs": "[1, 3, 5, 6]",
                "target": 5
            },
            "expected": 2,
            "unexpected": [
                0,
                1,
                3,
                4
            ]
        },
        {
            "input": {
                "xs": "[1, 3, 5, 6]",
                "target": 2
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
                "xs": "[1, 3, 5, 6]",
                "target": 7
            },
            "expected": 4,
            "unexpected": [
                2,
                3
            ]
        },
        {
            "input": {
                "xs": "[1, 3, 5, 6]",
                "target": 0
            },
            "expected": 0,
            "unexpected": [
                1,
                2
            ]
        },
        {
            "input": {
                "xs": "[]",
                "target": 3
            },
            "expected": 0,
            "unexpected": [
                1
            ]
        },
        {
            "input": {
                "xs": "[10]",
                "target": 5
            },
            "expected": 0,
            "unexpected": [
                1
            ]
        },
        {
            "input": {
                "xs": "[10]",
                "target": 15
            },
            "expected": 1,
            "unexpected": [
                0
            ]
        }
    ]
    */
}