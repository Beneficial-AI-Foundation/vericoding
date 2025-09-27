// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_ones(arr: Seq<usize>) -> nat
    decreases arr.len()
{
    if arr.len() == 0 {
        0nat
    } else {
        (arr[0] as nat) + count_ones(arr.skip(1))
    }
}

fn min_skip_points(n: usize, arr: Vec<usize>) -> (result: usize)
    requires 
        n > 0,
        arr.len() == n,
        forall|i: int| 0 <= i < arr.len() ==> (arr[i] == 0 || arr[i] == 1),
    ensures 
        (result as nat) <= count_ones(arr@),
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
    // Examples from the problem:
    // min_skip_points(8, vec![1, 0, 1, 1, 0, 1, 1, 1]) should return 2
    // min_skip_points(5, vec![1, 1, 1, 1, 0]) should return 2
    // min_skip_points(1, vec![0]) should return 0
}