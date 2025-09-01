use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    let n: usize = a.len();
    let mut idx: usize = 0;
    let mut res: usize = 0;
    let mut found: bool = false;
    while idx < n
        invariant idx <= n,
        invariant (!found) ==> (forall |j: int| 0 <= j && j < idx as int ==> a[j as usize] != elem),
        invariant found ==> (res < idx && a[res] == elem && (forall |j: int| 0 <= j && j < idx as int ==> (a[j as usize] == elem ==> j <= res as int))),
    {
        if a[idx] == elem {
            res = idx;
            found = true;
        }
        idx = idx + 1;
    }
    proof {
        // from loop termination idx == n
        assert(idx == n);
        // if not found, then by invariant no element in [0, n)
        if !found {
            assert(forall |j: int| 0 <= j && j < n as int ==> a[j as usize] != elem);
            // hence no such element exists, contradicting precondition
            assert(!(exists |i: int| 0 <= i && i < n as int && a[i as usize] == elem));
            assert(exists |i: int| 0 <= i && i < n as int && a[i as usize] == elem); // from precondition
            assert(false);
        }
    }
    // Now found is provably true, and the invariant for found with idx == n gives required postconditions
    res
}
// </vc-code>

fn main() {}
}