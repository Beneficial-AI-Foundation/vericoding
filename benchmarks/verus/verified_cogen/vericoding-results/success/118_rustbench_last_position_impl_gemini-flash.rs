// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = a.len() - 1;
    while i >= 0
        invariant
            0 <= i < a.len(),
            exists|k: int| 0 <= k < a.len() && a[k] == elem,
            forall|l: int| (i < l < a.len()) ==> a[l] != elem,
        decreases i
    {
        if a[i] == elem {
            return i;
        }
        i = i - 1;
    }
    // This part should not be reachable due to the `exists` precondition
    // but we need to return something to satisfy the type system.
    // Since the precondition `exists|i: int| 0 <= i < a.len() && a[i] == elem`
    // guarantees that `elem` is present in the array, the loop will always find it.
    // We return 0 as a placeholder, though it will never be reached.
    0
}
// </vc-code>

}
fn main() {}