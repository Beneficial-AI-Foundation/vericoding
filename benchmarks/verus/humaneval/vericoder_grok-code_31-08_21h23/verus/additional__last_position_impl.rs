use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    let len: usize = a.len();
    let mut result: usize = 0;
    let mut found = false;
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i as int <= len as int,
            found ==> (result as int) < (i as int) && a@[result as int] == elem,
            found ==> forall|j: int| #[trigger] (0 <= j < result as int) ==> a@[j] != elem,
            found ==> forall|j: int| #[trigger] ((result as int) < j < i as int) ==> a@[j] != elem,
            !found ==> forall|j: int| #[trigger] (0 <= j < i as int) ==> a@[j] != elem,
    {
        if a[i] == elem {
            result = i;
            found = true;
        }
        i += 1;
    }
    assert(found);
    result
}
// </vc-code>

fn main() {}
}