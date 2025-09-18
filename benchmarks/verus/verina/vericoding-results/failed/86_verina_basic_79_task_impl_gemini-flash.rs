// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): Fixed type mismatch in while loop invariant a[j] and a[max_idx] by casting to `int` when indexing*/
    let mut max_val = a[x];
    let mut max_idx = x;
    let mut i = x + 1;

    while i < a.len()
        invariant
            x <= max_idx && max_idx < i,
            x < a.len(),
            i <= a.len(),
            (forall|j: int| x <= j && j < i ==> a[j as usize] <= max_val),
            a[max_idx] == max_val,
    {
        if a[i] > max_val {
            max_val = a[i];
            max_idx = i;
        }
        i = i + 1;
    }

    (max_val, max_idx)
}
// </vc-code>

}
fn main() {}