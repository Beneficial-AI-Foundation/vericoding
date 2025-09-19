// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
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
    // /*
    // -- Invalid Inputs
    // [
    //     {
    //         "input": {
    //             "a": "#[1, 2, 3, 4]",
    //             "b": "#[5, 6, 7]"
    //         }
    //     }
    // ]
    // -- Tests
    // [
    //     {
    //         "input": {
    //             "a": "#[1, 2, 3]",
    //             "b": "#[4, 5, 6]"
    //         },
    //         "expected": "#[5, 7, 9]",
    //         "unexpected": [
    //             "#[5, 6, 9]",
    //             "#[4, 7, 9]"
    //         ]
    //     },
    //     {
    //         "input": {
    //             "a": "#[0, 0, 0]",
    //             "b": "#[0, 0, 0]"
    //         },
    //         "expected": "#[0, 0, 0]",
    //         "unexpected": [
    //             "#[0, 0, 1]",
    //             "#[1, 0, 0]"
    //         ]
    //     },
    //     {
    //         "input": {
    //             "a": "#[-1, 2, 3]",
    //             "b": "#[1, -2, 4]"
    //         },
    //         "expected": "#[0, 0, 7]",
    //         "unexpected": [
    //             "#[0, 1, 7]",
    //             "#[0, 0, 6]"
    //         ]
    //     },
    //     {
    //         "input": {
    //             "a": "#[10]",
    //             "b": "#[-10]"
    //         },
    //         "expected": "#[0]",
    //         "unexpected": [
    //             "#[1]",
    //             "#[-1]"
    //         ]
    //     },
    //     {
    //         "input": {
    //             "a": "#[100, 200, 300]",
    //             "b": "#[100, 200, 300]"
    //         },
    //         "expected": "#[200, 400, 600]",
    //         "unexpected": [
    //             "#[200, 400, 601]",
    //             "#[199, 400, 600]",
    //             "#[200, 399, 600]"
    //         ]
    //     }
    // ]
    // */
}