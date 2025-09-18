// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prefix count of nonzeros in a sequence */
spec fn prefix_nonzero_count(s: Seq<i32>, n: int) -> int
    decreases n
{ if n <= 0 { 0 } else { prefix_nonzero_count(s, n - 1) + if s@[n - 1] != 0 { 1 } else { 0 } } }
// </vc-helpers>

// <vc-spec>
fn count_nonzero(a: Vec<i32>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> count < a.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): loop counting nonzeros with invariant relating cnt to prefix_nonzero_count */
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    while i < a.len()
        invariant i <= a.len(),
        invariant cnt <= a.len(),
        invariant prefix_nonzero_count(a@, i as int) == cnt as int,
        decreases a.len() - i
    {
        if a[i] != 0 {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    cnt
}
// </vc-code>

}
fn main() {}