// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): convert usize to int for specs */
spec fn to_int(u: usize) -> int { u as int }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn binary_search(arr: &[i32], target: i32) -> (result: Option<usize>)
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    ensures
        match result {
            Some(index) => arr[index as int] == target && arr.len() > 0 && index < arr.len(),
            None => forall|i: int| 0 <= i && i < arr.len() ==> arr[i] != target,
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use usize indices and spec conversions */
    let n: usize = arr.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall|j: int| 0 <= j && j < to_int(i) ==> arr@[j] != target,
        decreases to_int(n) - to_int(i)
    {
        if arr[i] == target {
            return Some(i);
        }
        i = i + 1;
    }
    None
}
// </vc-code>

}
fn main() {}