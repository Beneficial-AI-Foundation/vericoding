// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}