// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): max2 returns the larger of two i32 values */
fn max2(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn max_of_list(lst: Vec<i32>) -> (result: i32)
    requires lst.len() > 0,
    ensures
        exists|i: int| 0 <= i < lst.len() && lst[i] == result,
        forall|i: int| 0 <= i < lst.len() ==> lst[i] <= result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implemented max search using usize loop and spec-level invariants */
    let mut i: usize = 1;
    let mut cur: i32 = lst[0];
    while i < lst.len()
        invariant
            0 <= (i as int),
            (i as int) <= lst.len() as int,
            forall |k: int| 0 <= k && k < (i as int) ==> lst@[k] <= cur,
            exists |j: int| 0 <= j && j < (i as int) && lst@[j] == cur,
        decreases (lst.len() as int) - (i as int)
    {
        let v = lst[i];
        if v > cur {
            cur = v;
        }
        i = i + 1;
    }
    cur
}
// </vc-code>

}
fn main() {}