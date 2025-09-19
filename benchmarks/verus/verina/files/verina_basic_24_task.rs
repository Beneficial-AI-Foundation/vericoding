// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: i32) -> bool {
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn first_even_odd_difference(a: &Vec<i32>) -> (result: i32)
    requires 
        a.len() > 1,
        exists|x: int| 0 <= x < a.len() && is_even(a[x as int]),
        exists|x: int| 0 <= x < a.len() && is_odd(a[x as int]),
    ensures 
        exists|i: int, j: int| 
            0 <= i < a.len() && 0 <= j < a.len() &&
            is_even(a[i as int]) && is_odd(a[j as int]) &&
            result == a[i as int] - a[j as int] &&
            (forall|k: int| 0 <= k < i ==> is_odd(a[k as int])) &&
            (forall|k: int| 0 <= k < j ==> is_even(a[k as int]))
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
                "a": "#[2]"
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "a": "#[2, 3, 4, 5]"
            },
            "expected": -1,
            "unexpected": [
                -2,
                1,
                -3
            ]
        },
        {
            "input": {
                "a": "#[1, 4, 6, 8]"
            },
            "expected": 3,
            "unexpected": [
                2,
                4,
                5
            ]
        },
        {
            "input": {
                "a": "#[7, 2, 9, 4]"
            },
            "expected": -5,
            "unexpected": [
                -3,
                -6,
                5
            ]
        },
        {
            "input": {
                "a": "#[2, 2, 3, 3]"
            },
            "expected": -1,
            "unexpected": [
                1,
                0,
                -2
            ]
        },
        {
            "input": {
                "a": "#[1, 1, 2, 2]"
            },
            "expected": 1,
            "unexpected": [
                0,
                2,
                -1
            ]
        }
    ]
    */
}