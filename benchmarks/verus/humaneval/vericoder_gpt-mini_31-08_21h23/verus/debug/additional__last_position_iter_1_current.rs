use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed.
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
    let mut i: usize = 0;
    let mut found: bool = false;
    let mut last: usize = 0usize;

    while i < a.len()
        invariant i <= a.len()
        invariant found == (exists |j: int| 0 <= j && j < i as int && a[j as usize] == elem)
        invariant (!found) || (last < i && a[last] == elem && forall |j: int| last as int < j && j < i as int ==> a[j as usize] != elem)
    {
        if a[i] == elem {
            last = i;
            found = true;

            // prove the existential for the new i (which will become i+1 after increment)
            // witness is j = i (old i)
            proof {
                let w: int = i as int;
                assert(0 <= w);
                assert(w < (i as int) + 1);
                assert(a[w as usize] == elem);
            }
        } else {
            // nothing to update; invariants will follow from previous invariant
        }

        i += 1;
    }

    // At loop exit i == a.len(). By the invariant, found == (exists j < a.len() . a[j]==elem).
    // From precondition we know such a j exists, hence found must be true.
    proof {
        assert(exists |j: int| 0 <= j && j < a.len() as int && a[j as usize] == elem);
        assert(found == (exists |j: int| 0 <= j && j < i as int && a[j as usize] == elem));
        // i == a.len()
        assert(i == a.len());
        assert(found);
    }

    // Now invariants give the required postconditions:
    // found ==> last < i && a[last]==elem && forall last<j<i ==> a[j]!=elem
    // with i == a.len() this matches the ensures.
    last
    // impl-end
}
// </vc-code>

fn main() {}
}