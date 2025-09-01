use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    // pre-conditions-start
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut i: int = a.len() as int - 1;
    let mut last_pos: int = 0; // Initialize with a dummy value, will be overwritten

    #[invariant]
    #[verifier::loop_invariant_check]
    while i >= 0
        invariant
            0 <= i < a.len() || i == -1,
            // If last_pos has been set, it holds the index of the rightmost `elem` found so far,
            // and all elements to its right are not `elem`.
            (last_pos != 0 ==> (
                0 <= last_pos < a.len() as int &&
                a[last_pos as int] == elem &&
                forall |k: int| #[trigger] (last_pos < k < a.len() as int) ==> a[k] != elem
            )),
            // If last_pos is 0, it means we haven't found a suitable element yet,
            // so all elements from 'i + 1' to 'a.len() - 1' must not be 'elem'.
            (last_pos == 0 ==> (
                forall |j: int| (i < j < a.len() as int) ==> a[j] != elem
            )),
    {
        if a[i as usize] == elem {
            last_pos = i;
            // When we find an `elem`, we update `last_pos` and break.
            // At this point, the loop invariant for `last_pos != 0` is established.
            // Specifically, `a[last_pos]` is `elem`.
            // And because we are iterating from right to left, all elements `k`
            // such that `last_pos < k < a.len()` have already been checked and found not equal to `elem`
            // (or they were not `elem` when `last_pos` was set in a previous iteration).
            proof {
                assert(0 <= last_pos < a.len() as int);
                assert(a[last_pos as int] == elem);
                assert(forall |k: int| (last_pos < k < a.len() as int) ==> a[k] != elem) by {
                    if last_pos + 1 < a.len() as int {
                        assert(forall |j: int| (last_pos < j < a.len() as int) ==> a[j] != elem); // from loop invariant when last_pos was 0
                    }
                }
            }
            break;
        }
        i = i - 1;
    }

    // According to the precondition, `elem` must exist in `a`.
    // Therefore, `last_pos` must have been set to a valid index by the end of the loop.
    // The `last_pos == 0` special initialization case is covered by the loop invariant.
    // If last_pos is not 0, it holds a valid index.
    // If the loop finished and last_pos is still 0, it means `elem` was not found
    // (which contradicts the precondition). So last_pos can't be 0 at the end.
    assert(last_pos != 0); // Directly follows from precondition: `elem` must be in `a`
    assert(0 <= last_pos < a.len() as int); // From loop invariant
    assert(a[last_pos as int] == elem); // From loop invariant
    assert(forall |k: int| (last_pos < k < a.len() as int) ==> a[k] != elem); // From loop invariant

    last_pos as usize
    // impl-end
}
// </vc-code>

fn main() {}
}