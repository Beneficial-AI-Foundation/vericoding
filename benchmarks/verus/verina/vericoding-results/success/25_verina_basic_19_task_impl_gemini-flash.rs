// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helper, no helper is needed */
// </vc-helpers>

// <vc-spec>
fn is_sorted(a: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] a[i] <= a[i + 1]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Simplified the invariant for `result` to remove the problematic `exists` quantifier and correctly track the sorted status up to `i`. */
{
    if a.len() <= 1 {
        true
    } else {
        let mut i = 0;
        while i < a.len() - 1
            invariant
                0 <= i <= a.len() - 1,
                (forall |j: int| 0 <= j < i ==> #[trigger] a[j] <= a[j + 1]),
            decreases (a.len() as int) - 1 - i as int
        {
            if a[i] > a[i+1] {
                return false;
            }
            i = i + 1;
        }
        true
    }
}
// </vc-code>

}
fn main() {}