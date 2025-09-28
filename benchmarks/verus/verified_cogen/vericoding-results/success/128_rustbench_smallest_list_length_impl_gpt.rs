// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define a simple min function on usize */
spec fn min_usize(a: usize, b: usize) -> usize { if a < b { a } else { b } }

/* helper modified by LLM (iteration 2): prove bounds properties for min_usize */
proof fn min_usize_bounds(a: usize, b: usize)
    ensures
        min_usize(a, b) <= a,
        min_usize(a, b) <= b,
{
    if a < b {
        assert(min_usize(a, b) == a);
    } else {
        assert(min_usize(a, b) == b);
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_list_length(lists: Vec<Vec<i32>>) -> (result: usize)
    requires
        lists.len() > 0,
    ensures
        exists|i: int| #![auto] 0 <= i < lists.len() && result == lists[i].len(),
        forall|i: int| #![auto] 0 <= i < lists.len() ==> result <= lists[i].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented min scan with proper int/usize handling in invariants */
    let n: usize = lists.len();
    let mut i: usize = 1;
    let mut min_idx: usize = 0;
    let mut min_len: usize = lists[min_idx].len();

    while i < n
        invariant
            1 <= i && i <= n,
            n == lists.len(),
            min_idx < i,
            min_idx < n,
            min_len == lists[min_idx as int].len(),
            forall|k: int| 0 <= k < i as int ==> min_len <= lists[k].len(),
        decreases n - i
    {
        let li = lists[i].len();
        if li < min_len {
            min_len = li;
            min_idx = i;
        }
        i = i + 1;
    }

    min_len
}
// </vc-code>

}
fn main() {}