// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no changes from previous iteration */
spec fn sorted_prefix(s: Seq<i32>, n: int) -> bool
    recommends 0 <= n <= s.len()
{
    forall|i: int, j: int| 0 <= i && i < j && j < n ==> s.index(i) <= s.index(j)
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
/* code modified by LLM (iteration 4): added a decreases clause to the while loop to prove termination */
{
    let mut i: usize = 1;
    while i < lst.len()
        invariant
            1 <= i <= lst.len(),
            sorted_prefix(lst.view(), i as int),
        decreases lst.len() - i,
    {
        if lst[i - 1] > lst[i] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}