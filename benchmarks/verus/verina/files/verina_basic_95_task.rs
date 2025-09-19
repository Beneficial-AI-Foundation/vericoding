// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap(arr: &Vec<i32>, i: usize, j: usize) -> (result: Vec<i32>)
    requires
        i < arr.len(),
        j < arr.len(),
    ensures
        result.len() == arr.len(),
        result[i as int] == arr[j as int],
        result[j as int] == arr[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> result[k] == arr[k],
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
    //             "arr": "[1, 2, 3, 4]",
    //             "i": -1,
    //             "j": 2
    //         }
    //     }
    // ]
    // -- Tests
    // [
    //     {
    //         "input": {
    //             "arr": "[1, 2, 3, 4, 5]",
    //             "i": 1,
    //             "j": 3
    //         },
    //         "expected": "[1, 4, 3, 2, 5]",
    //         "unexpected": [
    //             "[1, 2, 3, 4, 5]",
    //             "[1, 3, 2, 4, 5]"
    //         ]
    //     },
    //     {
    //         "input": {
    //             "arr": "[10, 20, 30, 40]",
    //             "i": 0,
    //             "j": 3
    //         },
    //         "expected": "[40, 20, 30, 10]",
    //         "unexpected": [
    //             "[10, 40, 30, 20]",
    //             "[10, 20, 40, 30]"
    //         ]
    //     },
    //     {
    //         "input": {
    //             "arr": "[7, 8, 9]",
    //             "i": 1,
    //             "j": 2
    //         },
    //         "expected": "[7, 9, 8]",
    //         "unexpected": [
    //             "[8, 7, 9]",
    //             "[9, 8, 7]"
    //         ]
    //     },
    //     {
    //         "input": {
    //             "arr": "[1, 2, 3, 4]",
    //             "i": 0,
    //             "j": 0
    //         },
    //         "expected": "[1, 2, 3, 4]",
    //         "unexpected": [
    //             "[1, 2, 4, 3]",
    //             "[4, 2, 3, 1]"
    //         ]
    //     },
    //     {
    //         "input": {
    //             "arr": "[-1, -2, -3]",
    //             "i": 0,
    //             "j": 2
    //         },
    //         "expected": "[-3, -2, -1]",
    //         "unexpected": [
    //             "[-1, -2, -3]",
    //             "[-3, -1, -2]"
    //         ]
    //     }
    // ]
    // */
}