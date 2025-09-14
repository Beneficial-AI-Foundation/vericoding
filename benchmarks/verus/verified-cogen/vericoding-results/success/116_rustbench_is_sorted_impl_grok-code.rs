// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No changes needed as helpers section is empty */
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
/* code modified by LLM (iteration 5): Added decreases clause to the while loop to correctly terminate */
    let mut result = true;
    let mut i = 0;
    while i < lst.len() - 1
        invariant
            0 <= i <= lst.len() - 1,
            result <==> forall|k: int, l: int| 0 <= k && k < l && l <= i ==> lst@[k] <= lst@[l],
        decreases (lst.len() - 1 - i)
    {
        let a = lst[i];
        let b = lst[i + 1];
        if a > b {
            result = false;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}