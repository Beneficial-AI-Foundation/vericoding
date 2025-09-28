// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [no helpers needed] */
// </vc-helpers>

// <vc-spec>
fn is_sorted(a: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] a[i] <= a[i + 1]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [handled short vecs and fixed loop conditions/invariants] */
    if a.len() < 2 {
        return true;
    }

    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            a.len() >= 2,
            0 <= i <= a.len() - 1,
            forall|j: int| 0 <= j < i ==> #[trigger] a.view().index(j) <= a.view().index(j + 1),
        decreases a.len() - 1 - i
    {
        if a[i] > a[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}