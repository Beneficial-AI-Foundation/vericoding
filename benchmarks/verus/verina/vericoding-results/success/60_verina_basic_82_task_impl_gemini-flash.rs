// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected loop invariants and postconditions for `remove_front_helper` to ensure proper verification. Specifically, `result.len()` is `i - 1` and `forall` quantifiers are adjusted to match the loop bounds. */
fn remove_front_helper(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i + 1],
{
    let mut result = Vec::new();
    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i,
            i <= a.len(),
            result.len() == i - 1,
            forall|j: int| 0 <= j < result.len() ==> result[j] == a[j + 1],
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn remove_front(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        a.len() > 0,
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i + 1],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): calls helper function `remove_front_helper` which now has full verification. Removed duplicate proof block from code. */
{
    let result = remove_front_helper(a);
    result
}
// </vc-code>

}
fn main() {}