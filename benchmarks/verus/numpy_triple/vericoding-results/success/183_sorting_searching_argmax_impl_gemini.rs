// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no changes */
spec fn is_first_argmax_in_prefix(a: Seq<i32>, idx: int, len: int) -> bool {
    0 <= idx < len &&
    (forall|j: int| 0 <= j < len ==> a[j] <= a[idx]) &&
    (forall|j: int| 0 <= j < len && a[j] == a[idx] ==> idx <= j)
}
// </vc-helpers>

// <vc-spec>
fn argmax(a: Vec<i32>) -> (result: usize)
    requires a.len() > 0,
    ensures 
        result < a.len(),
        forall|j: int| 0 <= j < a.len() ==> a[j] <= a[result as int],
        forall|j: int| 0 <= j < a.len() && a[j] == a[result as int] ==> result <= j as usize,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to loop */
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            a.len() > 0,
            1 <= i <= a.len(),
            is_first_argmax_in_prefix(a.view(), max_idx as int, i as int),
        decreases a.len() - i
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    max_idx
}
// </vc-code>

}
fn main() {}