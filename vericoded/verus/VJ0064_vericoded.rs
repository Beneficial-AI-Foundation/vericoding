// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove transitivity on usize inequalities */
proof fn lt_le_implies_le(a: usize, b: usize, c: usize)
    requires
        a < b,
        b <= c,
    ensures
        a <= c
{
}

/* helper modified by LLM (iteration 2): deterministic minimum on usize values */
fn usize_min(a: usize, b: usize) -> (m: usize)
    ensures
        m == a || m == b,
        m <= a,
        m <= b
{
    if a <= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)

    requires
        list.len() > 0,

    ensures
        min >= 0,
        forall|i: int| 0 <= i < list.len() ==> min <= #[trigger] list[i].len(),
        exists|i: int| 0 <= i < list.len() && min == #[trigger] list[i].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented min-scan loop with correct int indexing in invariants */
    let n = list.len();
    let mut idx: usize = 0;
    let mut min_len: usize = list[0].len();

    while idx + 1 < n
        invariant
            n == list.len(),
            0 < n,
            idx < n,
            forall|k: int| 0 <= k <= idx as int && k < list.len() ==> min_len <= #[trigger] list[k].len(),
            exists|k: int| 0 <= k <= idx as int && k < list.len() && min_len == #[trigger] list[k].len(),
        decreases n - 1 - idx
    {
        let next = idx + 1;
        let cur = list[next].len();
        if cur < min_len {
            min_len = cur;
        }
        idx = next;
    }

    min_len
}
// </vc-code>

}
fn main() {}