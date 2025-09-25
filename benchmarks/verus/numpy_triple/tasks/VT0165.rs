// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn argmax(arr: &Vec<i8>) -> (result: usize)
    requires arr.len() > 0,
    ensures 
        result < arr.len(),
        forall|i: int| 0 <= i && i < arr.len() ==> arr@[i] <= arr@[result as int],
        forall|i: int| 0 <= i && i < result as int ==> arr@[i] < arr@[result as int],
        forall|i: int| (result as int) < i && i < arr.len() ==> arr@[i] <= arr@[result as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}