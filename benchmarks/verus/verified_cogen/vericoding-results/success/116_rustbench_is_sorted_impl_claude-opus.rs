// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_sorted(lst: &[i32]) -> (result: bool)
    requires
        lst.len() >= 1,
    ensures
        result <== forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j],
        !result ==> exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    while i < lst.len() - 1
        invariant
            0 <= i <= lst.len() - 1,
            forall|k: int, l: int| 0 <= k && k < l && l <= i ==> lst[k] <= lst[l],
        decreases lst.len() - 1 - i
    {
        if lst[i] > lst[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}