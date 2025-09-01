use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
    // post-conditions-end
// </vc-spec>
// <vc-code>
#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
    // post-conditions-end
{
    // impl-start
    let mut max_idx: usize = 0;
    let mut i: usize = 1;

    while i < a.len()
        // invariants-start
        invariant
            0 <= max_idx < a.len(),
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] <= a[max_idx as int],
            0 <= i,
        // invariants-end
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i += 1;
    }

    assert(forall|k: int| 0 <= k < a.len() ==> a[k] <= a[max_idx as int]) by {
        // The loop invariant ensures this at the end
    };
    max_idx
    // impl-end
}
// </vc-code>

fn main() {}
}