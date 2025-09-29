// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): basic ordering facts for i8 */
proof fn lt_implies_le_i8(x: i8, y: i8)
    ensures
        x < y ==> x <= y,
{}

/* helper modified by LLM (iteration 2): transitivity of <= for i8 */
proof fn le_trans_i8(x: i8, y: i8, z: i8)
    ensures
        x <= y && y <= z ==> x <= z,
{}
// </vc-helpers>

// <vc-spec>
fn numpy_argmin(a: Vec<i8>) -> (result: usize)
    requires a.len() > 0,
    ensures 
        result < a.len(),
        forall|j: int| 0 <= j < a@.len() ==> a@[result as int] <= a@[j],
        forall|j: int| 0 <= j < a@.len() && a@[j] == a@[result as int] ==> (result as int) <= j,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement argmin with min_val and loop invariants; fix index preconditions and tie-breaking */
    let n: usize = a.len();
    assert(a.len() > 0);

    let mut res: usize = 0;
    assert(0 < a.len());
    let mut min_val: i8 = a[0];
    let mut i: usize = 1;

    while i < n
        invariant
            n == a.len(),
            1 <= a@.len(),
            1 <= i <= n,
            res < i,
            a@[res as int] == min_val,
            forall|j: int| 0 <= j < i as int ==> min_val <= a@[j],
            forall|j: int| 0 <= j < i as int && a@[j] == min_val ==> (res as int) <= j,
        decreases n - i
    {
        assert(i < a.len());
        assert(res < i);
        assert(i <= n);
        assert(n == a.len());
        assert(res < a.len());

        let curr: i8 = a[i];

        if curr < min_val {
            let old_i = i;
            // update res and min_val to reflect new minimum at position i
            res = i;
            min_val = curr;
            proof {
                // For j < old_i, we had min_val_old <= a[j]. Since curr < min_val_old, we get curr <= a[j].
                // For j == old_i, min_val == a[old_i] holds by assignment.
            }
        } else if curr == min_val {
            // Keep earliest index for ties: need res <= old i for the new j = old i case
            proof {
                assert((res as int) < (i as int));
            }
        } else {
            // curr > min_val: nothing to update; min_val <= curr holds trivially
        }

        i = i + 1;
        assert(i <= n);
    }

    // After loop: i == n == a.len(), and invariants give the postconditions
    proof {
        assert(i >= n);
        assert(i <= n);
        assert(i == n);
        assert(n == a.len());
    }

    res
}
// </vc-code>


}
fn main() {}