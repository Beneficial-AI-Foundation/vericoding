// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum_and_average(n: u32) -> (result: (u32, f64))
    requires n < 100000, /* reasonable bound to prevent overflow */
    ensures
        n == 0 ==> result.0 == 0,
        n > 0 ==> result.0 == (n * (n + 1)) / 2,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    (0u32, 0.0)
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
                "n": 5
            },
            "expected": "(15, 3.0)",
            "unexpected": [
                "(14, 2.8)",
                "(16, 3.2)"
            ]
        },
        {
            "input": {
                "n": 1
            },
            "expected": "(1, 1.0)",
            "unexpected": [
                "(0, 0.0)",
                "(2, 2.0)"
            ]
        },
        {
            "input": {
                "n": 10
            },
            "expected": "(55, 5.5)",
            "unexpected": [
                "(50, 5.0)",
                "(60, 6.0)"
            ]
        },
        {
            "input": {
                "n": 0
            },
            "expected": "(0, 0.0)",
            "unexpected": [
                "(1, 0.1)",
                "(-1, -0.1)"
            ]
        },
        {
            "input": {
                "n": 2
            },
            "expected": "(3, 1.5)",
            "unexpected": [
                "(2, 1.0)",
                "(4, 2.0)"
            ]
        }
    ]
    */
}