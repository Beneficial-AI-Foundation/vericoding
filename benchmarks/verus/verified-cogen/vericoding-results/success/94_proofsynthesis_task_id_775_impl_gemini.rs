// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn check_parity_recursive(arr: &Vec<usize>, i: usize) -> (result: bool)
    requires
        0 <= i <= arr.len(),
    ensures
        result == forall|j: int| i <= j < arr.len() ==> ((j % 2) == (arr[j] % 2)),
    decreases arr.len() - i,
{
    if i >= arr.len() {
        true
    } else {
        if (i % 2) == (arr[i] % 2) {
            check_parity_recursive(arr, i + 1)
        } else {
            false
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn is_odd_at_odd_index(arr: &Vec<usize>) -> (result: bool)

    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
// </vc-spec>
// <vc-code>
{
    check_parity_recursive(arr, 0)
}
// </vc-code>

}
fn main() {}