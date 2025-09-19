// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(a: &Vec<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        result == sum_to(a, a.len() as int),
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
            "expected": 15,
            "unexpected": [
                14,
                10,
                16
            ]
        },
        {
            "input": {
                "a": "#[13, 14, 15, 16, 17]"
            },
            "expected": 75,
            "unexpected": [
                74,
                76,
                70
            ]
        },
        {
            "input": {
                "a": "#[-1, -2, -3]"
            },
            "expected": -6,
            "unexpected": [
                -5,
                -7,
                0
            ]
        },
        {
            "input": {
                "a": "#[10, -10]"
            },
            "expected": 0,
            "unexpected": [
                5,
                -5,
                10
            ]
        }
    ]
    */
}