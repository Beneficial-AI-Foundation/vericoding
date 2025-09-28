// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no additional helpers needed */
// </vc-helpers>

// <vc-spec>
fn is_sorted(a: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] a[i] <= a[i + 1]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed forall syntax in invariant by adding ==> after range condition */
    if a.len() <= 1 {
        return true;
    }
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            i <= a.len() - 1,
            forall |k: int| 0 <= k < i ==> #[trigger] a[k] <= a[k + 1]
        decreases (a.len() - 1 - i)
    {
        if !(a[i] <= a[i + 1]) {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}