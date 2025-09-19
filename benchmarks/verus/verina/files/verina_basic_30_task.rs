// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
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
    // Invalid Inputs
    // [
    //     {
    //         "input": {
    //             "a": "[1]",
    //             "b": "[4, 0]"
    //         }
    //     }
    // ]
    // Tests
    // [
    //     {
    //         "input": {
    //             "a": "[10, 20, 30]",
    //             "b": "[3, 7, 5]"
    //         },
    //         "expected": "[1, 6, 0]",
    //         "unexpected": [
    //             "[1, 0, 0]",
    //             "[0, 6, 0]"
    //         ]
    //     },
    //     {
    //         "input": {
    //             "a": "[100, 200, 300, 400]",
    //             "b": "[10, 20, 30, 50]"
    //         },
    //         "expected": "[0, 0, 0, 0]",
    //         "unexpected": [
    //             "[0, 0, 0, 1]",
    //             "[1, 0, 0, 0]"
    //         ]
    //     },
    //     {
    //         "input": {
    //             "a": "[-10, -20, 30]",
    //             "b": "[3, -7, 5]"
    //         },
    //         "expected": "[2, 1, 0]",
    //         "unexpected": [
    //             "[-1, -5, 0]",
    //             "[-1, -6, 1]",
    //             "[0, -6, 0]"
    //         ]
    //     }
    // ]
}