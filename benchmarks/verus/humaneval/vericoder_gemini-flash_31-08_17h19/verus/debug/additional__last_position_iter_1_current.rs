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
    let mut i = a.len() as int - 1;
    let mut last_pos: int = 0; // Initialize with a dummy value, will be overwritten

    #[invariant(
        last_pos_is_elem_or_dummy_if_not_found == (a[last_pos as int] == elem || last_pos == 0),
        forall |j: int| i < j < a.len() ==> a[j] != elem,
        0 <= i < a.len() || i == -1,
        // The first element `result` such that `a[result] == elem` and all elements
        // from `result + 1` to `a.len() - 1` are not equal to `elem`.
        // This is only true if elem has already been found.
        (last_pos != 0 ==> (0 <= last_pos < a.len() && a[last_pos as int] == elem && forall |k: int| #[trigger] (last_pos < k < a.len()) ==> a[k] != elem)),
    )]
    while i >= 0
    {
        if a[i as usize] == elem {
            last_pos = i;
            break;
        }
        i = i - 1;
    }

    assert(0 <= last_pos < a.len());
    assert(a[last_pos as int] == elem);
    assert(forall |k: int| (last_pos < k < a.len()) ==> a[k] != elem);

    last_pos as usize
    // impl-end
}
// </vc-code>

fn main() {}
}