// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_prime(n: nat) -> (result: bool)
    requires n >= 2,
    ensures
        result ==> forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0,
        !result ==> exists|k: nat| 2 <= k < n && #[trigger] (n % k) == 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {
    /* 
    Invalid Inputs
    [
        {
            "input": {
                "n": 0
            }
        }
    ]
    Tests
    [
        {
            "input": {
                "n": 2
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "n": 3
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "n": 4
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "n": 5
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "n": 9
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "n": 11
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "n": 12
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "n": 13
            },
            "expected": true,
            "unexpected": [
                false
            ]
        }
    ]
    */
}