// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected type mismatch to allow `i32` indexing. */
spec fn is_max_at(a: &Vec<i32>, x: usize, idx: usize) -> bool {
    forall|i: int| (0 <= i && (i as usize) < idx ==> (a[i as usize]) <= (a[idx as usize]))
}
// </vc-helpers>

// <vc-spec>
fn online_max(a: &Vec<i32>, x: usize) -> (result: (i32, usize))
    requires
        a.len() > 0,
        x < a.len(),
    ensures
        ({
            let (m, p) = result;
            x <= p && p < a.len()
            && (forall|i: int| 0 <= i < x ==> a[i] <= m)
            && (exists|i: int| 0 <= i < x && a[i] == m)
            && ((p < a.len() - 1) ==> (exists|i: int| x <= i <= p && a[i] > m))
            && ((forall|i: int| x <= i < a.len() ==> a[i] <= m) ==> p == a.len() - 1)
        })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implemented the online_max algorithm and fixed loop invariants. */
{
    let mut max_val: i32 = a[0];
    let mut max_idx: usize = 0;

    while max_idx < x
        invariant
            x < a.len(),
            max_idx <= x,
            max_idx < a.len(),
            forall|j: int| (0 <= j && (j as usize) < max_idx ==> (a[j as usize]) <= max_val),
            exists|j: int| (0 <= j && (j as usize) < max_idx && (a[j as usize]) == max_val),

    {
        if a[max_idx] > max_val {
            max_val = a[max_idx];
            max_idx = max_idx;
        } else {
          max_idx = max_idx;
        }
        max_idx = max_idx + 1;
    }

    let mut k = x;
    while k < a.len()
        invariant
            x < a.len(),
            k <= a.len(),
            max_idx < a.len(),
            forall|j: int| (0 <= j && (j as usize) < x ==> a[j as usize] <= max_val),
            exists|j: int| (0 <= j && (j as usize) < x && a[j as usize] == max_val),
            forall|j: int| (x <= j && (j as usize) < k ==> a[j as usize] <= max_val),

    {
        if a[k] >= max_val {
            max_val = a[k];
            max_idx = k;
        }
        k = k + 1;
    }

    (max_val, max_idx)
}
// </vc-code>

}
fn main() {}