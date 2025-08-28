use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_sorted(lst: &[i32]) -> (result: bool)
    // pre-conditions-start
    requires
        lst.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <== forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j],
        !result ==> exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    while i < lst.len() - 1
        invariant
            lst.len() >= 1,
            i < lst.len(),
            forall|k: int| #![trigger lst[k]] 0 <= k && k < i ==> lst[k] <= lst[k + 1],
        decreases
            lst.len() - 1 - i,
    {
        if lst[i] > lst[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {}
}