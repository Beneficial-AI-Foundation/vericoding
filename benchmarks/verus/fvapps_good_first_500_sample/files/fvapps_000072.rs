// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_non_decreasing(arr: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

fn make_non_decreasing(arr: Vec<usize>) -> (result: (usize, Vec<usize>))
    requires arr.len() >= 3,
            forall|i: int| 0 <= i < arr.len() ==> arr[i] <= arr.len(),
    ensures 
        result.1.len() <= 2 * arr.len(),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    (0, Vec::new())
    // impl-end
}
// </vc-code>


}
fn main() {}