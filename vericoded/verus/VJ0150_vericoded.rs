// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sorted_up_to(lst: &[i32], k: int) -> bool
{
    forall|i: int, j: int| 0 <= i && i < j && j < k ==> lst[i] <= lst[j]
}
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
    /* code modified by LLM (iteration 3): added decreases clause to fix compilation error */
    let mut i = 1;
    while i < lst.len()
        invariant
            1 <= i <= lst.len(),
            sorted_up_to(lst, i as int),
        decreases lst.len() - i
    {
        if lst[i - 1] > lst[i] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}