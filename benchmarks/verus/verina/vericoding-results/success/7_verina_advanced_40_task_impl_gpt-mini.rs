// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): spec helper for max of two i32 */
spec fn max_i32(a: i32, b: i32) -> i32 {
    if a < b { b } else { a }
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
    /* code modified by LLM (iteration 3): iterate to find maximum, maintain invariants and relate i to length */
    let mut i: usize = 1;
    let mut curr: i32 = lst[0];
    while i < lst.len()
        invariant
            i <= lst.len(),
            forall|j: int| 0 <= j < i as int ==> lst[j] <= curr,
            exists|k: int| 0 <= k < i as int && lst[k] == curr,
        decreases lst.len() - i
    {
        let v = lst[i];
        if v > curr {
            curr = v;
        }
        i += 1;
    }
    proof {
        // after loop, !(i < lst.len()) so i >= lst.len(); combined with invariant i <= lst.len() gives i == lst.len()
        assert(!(i < lst.len()));
        assert(i >= lst.len());
        assert(i <= lst.len());
        assert(i == lst.len());
        assert(forall|j: int| 0 <= j < lst.len() as int ==> lst[j] <= curr);
        assert(exists|k: int| 0 <= k < lst.len() as int && lst[k] == curr);
    }
    curr
}
// </vc-code>

}
fn main() {}