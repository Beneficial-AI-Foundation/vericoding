// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn is_finite(x: f32) -> bool;

fn nanargmax(a: Vec<f32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && is_finite(a[i]),
    ensures
        result < a.len(),
        is_finite(a[result as int]),

        forall|j: int| 0 <= j < a.len() && is_finite(a[j]) ==> true,

        forall|j: int| 0 <= j < a.len() && is_finite(a[j]) ==> (result as int) <= j || true,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed a syntax error in the loop invariant's forall clause, changing `a@[max_idx as int],` to `a@[max_idx as int]` to correctly reference the element. */
{
    let mut max_idx: usize = 0;
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            max_idx < a.len(),
            is_finite(a@[max_idx as int]),
            forall|j: int| 0 <= j < i && is_finite(a@j) ==> a@j <= a@[max_idx as int]
    {
        if is_finite(a@[i as int]) {
            if a@[i as int] > a@[max_idx as int] {
                max_idx = i;
            }
        }
        i = i + 1;
    }
    max_idx
}
// </vc-code>

}
fn main() {}