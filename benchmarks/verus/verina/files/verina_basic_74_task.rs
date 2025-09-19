// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_array_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}
// </vc-preamble>

// <vc-helpers>
fn max_array_aux(a: &Vec<i32>, index: usize, current: i32) -> (result: i32)
    requires index <= a.len(),
    decreases a.len() - index,
{
    if index < a.len() {
        let new_current = if current > a[index] { current } else { a[index] };
        max_array_aux(a, index + 1, new_current)
    } else {
        current
    }
}
// </vc-helpers>

// <vc-spec>
fn max_array(a: &Vec<i32>) -> (result: i32)
    requires max_array_precond(a),
    ensures
        forall|k: int| 0 <= k < a.len() ==> result >= a[k],
        exists|k: int| 0 <= k < a.len() && result == a[k],
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
    [
        {
            "input": {
                "a": "[]"
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "a": "[1, 2, 3, 4, 5]"
            },
            "expected": 5,
            "unexpected": [
                4,
                3
            ]
        },
        {
            "input": {
                "a": "[5, 3, 4, 1, 2]"
            },
            "expected": 5,
            "unexpected": [
                4,
                3,
                2
            ]
        },
        {
            "input": {
                "a": "[7]"
            },
            "expected": 7,
            "unexpected": [
                6,
                8
            ]
        },
        {
            "input": {
                "a": "[-1, -5, -3, -4]"
            },
            "expected": -1,
            "unexpected": [
                -3,
                -4
            ]
        },
        {
            "input": {
                "a": "[-10, -20, -30, -5, -15]"
            },
            "expected": -5,
            "unexpected": [
                -10,
                -15,
                -20
            ]
        }
    ]
    */
}