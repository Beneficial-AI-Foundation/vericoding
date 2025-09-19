// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn smallest_missing_number(s: Seq<nat>) -> nat;
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0 as nat
    // impl-end
}

proof fn smallest_missing_number_spec_satisfied(s: Seq<nat>)
    requires forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
    ensures
        !s.contains(smallest_missing_number(s)),
        forall|k: nat| k < smallest_missing_number(s) ==> s.contains(k),
{
    assume(false); /* TODO: Remove this line and implement the proof */
}
// </vc-code>


}
fn main() {
    /* 
    -- Invalid Inputs
    [
        {
            "input": {
                "s": "[3, 2, 1]"
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "s": "[0, 1, 2, 6, 9]"
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
                "s": "[4, 5, 10, 11]"
            },
            "expected": 0,
            "unexpected": [
                1,
                2
            ]
        },
        {
            "input": {
                "s": "[0, 1, 2, 3, 4, 5]"
            },
            "expected": 6,
            "unexpected": [
                5,
                7
            ]
        },
        {
            "input": {
                "s": "[]"
            },
            "expected": 0,
            "unexpected": [
                1,
                2
            ]
        },
        {
            "input": {
                "s": "[0, 2, 3, 4]"
            },
            "expected": 1,
            "unexpected": [
                0,
                2,
                3
            ]
        }
    ]
    */
}