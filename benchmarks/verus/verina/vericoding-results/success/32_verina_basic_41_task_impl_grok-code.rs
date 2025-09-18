// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No helper needed */

// </vc-helpers>

// <vc-spec>
fn has_only_one_distinct_element(a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0,
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]),
        !result ==> (exists|i: int| 0 <= i < a.len() && #[trigger] a[i] != a[0]),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): Added #[trigger] to forall in invariant to resolve quantifier trigger error */
    let mut i = 1;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall |k: int| #[trigger] a[k] == a[0] <== 0 <= k < i
        decreases a.len() - i
    {
        if a[i] != a[0] {
            return false;
        }
        i += 1;
    }
    return true;
}
// </vc-code>

}
fn main() {}