// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for all elements in the first k positions being less than t */
spec fn all_prefix_lt(l: &[i32], k: int, t: i32) -> bool {
    0 <= k && k <= l.len() as int && forall|i: int| 0 <= i < k ==> l[i] < t
}
// </vc-helpers>

// <vc-spec>
fn below_threshold(l: &[i32], t: i32) -> (result: bool)

    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i] < t,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize index with invariant linking res and prefix property */
    let mut i: usize = 0;
    let mut res: bool = true;
    while i < l.len()
        invariant
            0 <= i as int,
            i as int <= l.len() as int,
            res == forall|j: int| 0 <= j < i as int ==> l[j] < t,
        decreases l.len() - i
    {
        let curr: i32 = l[i];
        res = res && (curr < t);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}