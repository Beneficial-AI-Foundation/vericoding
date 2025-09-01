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
            // The first element `result` such that `a[result] == elem` and all elements
            // from `result + 1` to `a.len() - 1` are not equal to `elem`.
            // This is only true if elem has already been found.
            (last_pos != 0 ==> (0 <= last_pos < a.len() as int && a[last_pos as int] == elem && forall |k: int| #[trigger] (last_pos < k < a.len() as int) ==> a[k] != elem)),
            // If last_pos is 0, it means we haven't found a suitable element yet,
            // so all elements from 'i + 1' to 'a.len() - 1' must not be 'elem'.
            (last_pos == 0 ==> (forall |j: int| i < j < a.len() as int ==> a[j] != elem)),
    {
        if a[i as usize] == elem {
            last_pos = i;
            // The post-conditions of the function are established at this point for last_pos.
            // We can break, and Verus will verify that these conditions hold.
            proof {
                assert (0 <= last_pos < a.len() as int);
                assert (a[last_pos as int] == elem);
                assert (forall |k: int| (last_pos < k < a.len() as int) ==> a[k] != elem);
            }
            break;
        }
        i = i - 1;
    }

    // After the loop, `last_pos` must satisfy the post-conditions.
    // The loop invariant, combined with the break condition, ensures this.
    // If the loop finished without breaking, it means 'elem' was not found
    // in the iterated part, but the precondition states it exists.
    assert(0 <= last_pos < a.len() as int);
    assert(a[last_pos as int] == elem);
    assert(forall |k: int| (last_pos < k < a.len() as int) ==> a[k] != elem);

    last_pos as usize
    // impl-end
}
// </vc-code>

fn main() {}
}