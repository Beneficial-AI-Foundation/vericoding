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
        invariant i <= a.len();
        invariant found == (exists|j: int| 0 <= j && j < i as int && a[j as usize] == elem);
        invariant (!found) || (last < i && a[last] == elem && forall|j: int| last as int < j && j < i as int ==> a[j as usize] != elem);
    {
        if a[i] == elem {
            last = i;
            found = true;

            proof {
                let w: int = i as int;
                assert(0 <= w);
                assert(w < (i as int) + 1);
                assert(a[w as usize] == elem);
                assert(exists|j: int| 0 <= j && j < (i as int) + 1 && a[j as usize] == elem);
            }
        } else {
            proof {
                // If a[i] != elem, then existence of an element equal to elem
                // among indices < i+1 is equivalent to existence among indices < i.
                assert(!(a[i] == elem));
                assert((exists|j: int| 0 <= j && j < i as int && a[j as usize] == elem) ==
                       (exists|j: int| 0 <= j && j < (i as int) + 1 && a[j as usize] == elem));
            }
        }

        i += 1;
    }

    proof {
        assert(exists|j: int| 0 <= j && j < a.len() as int && a[j as usize] == elem);
        assert(found == (exists|j: int| 0 <= j && j < i as int && a[j as usize] == elem));
        assert(i == a.len());
        assert(found);

        // From the invariant when found is true
        assert(last < i);
        assert(a[last] == elem);
        assert(forall|j: int| last as int < j && j < i as int ==> a[j as usize] != elem);
    }

    last
    // impl-end
}
// </vc-code>

fn main() {}
}