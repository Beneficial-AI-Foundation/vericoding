// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_perfect_square(n: nat) -> bool {
    exists|i: nat| #[trigger] (i * i) == n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_perfect_square_fn(n: u64) -> (result: bool)
    ensures result <==> is_perfect_square(n as nat),
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
    []
    Tests
    [
        {
            "input": {
                "n": 0
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "n": 1
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
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "n": 9
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "n": 2
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "n": 3
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "n": 10
            },
            "expected": false,
            "unexpected": [
                true
            ]
        },
        {
            "input": {
                "n": 16
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "n": 25
            },
            "expected": true,
            "unexpected": [
                false
            ]
        },
        {
            "input": {
                "n": 26
            },
            "expected": false,
            "unexpected": [
                true
            ]
        }
    ]
    */
}