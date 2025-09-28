// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): presence predicate over pervasive sequence */
spec fn present(s: pervasive::seq::Seq<i32>, idx: int, cur: int) -> bool { forall|k: int| 0 <= k < cur ==> exists|j: int| 0 <= j < idx && #[trigger] s@[j] == k as i32 }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        s.len() <= 100_000,
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v && s[k] != v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): linear scan ensuring presence predicate with triggers */
    let mut idx: usize = 0;
    let mut cur: i32 = 0;
    while idx < s.len()
        invariant
            0 <= cur as int,
            cur as int <= idx as int,
            present(s@, idx as int, cur as int),
            forall|j: int| 0 <= j < idx as int ==> s[j] != cur,
        decreases s.len() - idx
    {
        let si: i32 = s[idx];
        if si < cur {
            idx += 1;
        } else if si == cur {
            idx += 1;
            cur += 1;
        } else {
            break;
        }
    }
    cur
}
// </vc-code>

}
fn main() {}