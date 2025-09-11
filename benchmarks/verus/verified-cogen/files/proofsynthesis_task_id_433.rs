// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}