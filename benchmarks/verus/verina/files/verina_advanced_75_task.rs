// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn spec_subarray_sum(sequence: Seq<i32>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end || start < 0 || end > sequence.len() {
        0
    } else if start + 1 == end {
        sequence[start] as int
    } else {
        sequence[start] as int + spec_subarray_sum(sequence, start + 1, end)
    }
}
// </vc-helpers>

// <vc-spec>
fn task_code(sequence: Vec<i32>) -> (result: i32)
    requires sequence.len() > 0,
    ensures 
        exists|start: int, end: int| 
            0 <= start < end <= sequence.len() && 
            result as int == spec_subarray_sum(sequence@, start, end) &&
            forall|s: int, e: int| (0 <= s < e <= sequence.len()) ==> 
                spec_subarray_sum(sequence@, s, e) <= result as int,
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
    []
    -- Tests
    [
        {
            "input": {
                "sequence": "[10, -4, 3, 1, 5, 6, -35, 12, 21, -1]"
            },
            "expected": 33,
            "unexpected": [
                32,
                34,
                0
            ]
        },
        {
            "input": {
                "sequence": "[2, 1, -4, 3, 4, -4, 6, 5, -5, 1]"
            },
            "expected": 14,
            "unexpected": [
                13,
                15,
                0
            ]
        },
        {
            "input": {
                "sequence": "[-1, -2, -3, -4, -5]"
            },
            "expected": -1,
            "unexpected": [
                -2,
                0,
                1
            ]
        },
        {
            "input": {
                "sequence": "[7]"
            },
            "expected": 7,
            "unexpected": [
                0,
                1,
                -7
            ]
        },
        {
            "input": {
                "sequence": "[1, 2, 3, 4, 5]"
            },
            "expected": 15,
            "unexpected": [
                14,
                16,
                0
            ]
        }
    ]
    */
}