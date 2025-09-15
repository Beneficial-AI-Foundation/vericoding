// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate for index range */
spec fn idx_in_range(i: int, len: int) -> bool { 0 <= i && i < len }
// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    requires exists|i: int| 0 <= i < a.len() && a[i] == e,
    ensures
        result < a.len(),
        a[result as int] == e,
        forall|k: int| 0 <= k < result ==> a[k] != e,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): linear search using witness index to prove first occurrence */
    let j = choose(|j: int| 0 <= j && j < a.len() && a[j] == e);
    let j_usize: usize = j as usize;
    let mut i: usize = 0;
    while i < j_usize
        invariant i <= j_usize,
        invariant forall|k: int| 0 <= k && k < (i as int) ==> a[k] != e,
        decreases j_usize - i
    {
        if a[i] == e {
            return i;
        }
        i = i + 1;
    }
    j_usize
}
// </vc-code>

}
fn main() {}