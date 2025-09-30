// <vc-preamble>
use vstd::prelude::*;

verus! {

fn binary_search(a: &[int], circle: int) -> (n: usize)
    requires
        forall|i: int| 1 <= i < a.len() ==> a[i-1] < #[trigger] a[i],
        forall|i: int, j: int| 0 <= i < j < a.len() ==> #[trigger] a[i] < #[trigger] a[j],
    ensures
        n <= a.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] a[i] < circle,
        forall|i: int| n <= i < a.len() ==> circle <= #[trigger] a[i],
{
    assume(false);
    0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): corrected requires clause */
proof fn lemma_not_in_if_not_at_pos(a: Seq<int>, val: int, n: int)
    requires
        forall|i: int, j: int| 0 <= i < j < a.len() ==> #[trigger] a[i] < #[trigger] a[j],
        0 <= n <= a.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] a[i] < val,
        forall|i: int| n <= i < a.len() ==> val <= #[trigger] a[i],
        (n < a.len()) ==> a[n] != val,
    ensures
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] != val,
{
}
// </vc-helpers>

// <vc-spec>
fn tangent(r: &[int], x: &[int]) -> (found: bool)
    requires
        forall|i: int| 1 <= i < x.len() ==> x[i-1] < #[trigger] x[i],
        forall|i: int, j: int| 0 <= i < j < x.len() ==> #[trigger] x[i] < #[trigger] x[j],
    ensures
        !found ==> forall|i: int, j: int| 
            0 <= i < r.len() && 0 <= j < x.len() ==> #[trigger] r[i] != #[trigger] x[j],
        found ==> exists|i: int, j: int|
            0 <= i < r.len() && 0 <= j < x.len() && #[trigger] r[i] == #[trigger] x[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added sortedness of x as loop invariants */
    let mut i: usize = 0;
    while i < r.len()
        invariant
            i <= r.len(),
            forall|k: int, j: int| 0 <= k < (i as int) && 0 <= j < x@.len()
                ==> #[trigger] r@[k] != #[trigger] x@[j],
            forall|j: int| 1 <= j < x@.len() ==> x@[j-1] < #[trigger] x@[j],
            forall|j: int, k: int| 0 <= j < k < x@.len() ==> #[trigger] x@[j] < #[trigger] x@[k],
        decreases r.len() - i
    {
        let val_r = r[i];
        let n = binary_search(x, val_r);

        if n < x.len() && x[n] == val_r {
            return true;
        } else {
            proof {
                lemma_not_in_if_not_at_pos(x@, val_r, n as int);
            }
        }

        i = i + 1;
    }

    false
}
// </vc-code>

}
fn main() {}