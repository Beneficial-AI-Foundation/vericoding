// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_not_equal_up_to(arr: &[i32], target: i32, n: int) -> bool { forall|k: int| 0 <= k && k < n ==> arr[k as int] != target }

proof fn lemma_lt_implies_nonzero(i: usize, len: usize)
    ensures i < len ==> 0 < len
{ }
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
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            forall|k: int| 0 <= k && k < i as int ==> arr[k as int] != target
        decreases arr.len() - i
    {
        if arr[i] == target {
            proof { lemma_lt_implies_nonzero(i, arr.len()); }
            return Some(i);
        } else {
            i = i + 1;
        }
    }
    None
}
// </vc-code>

}
fn main() {}