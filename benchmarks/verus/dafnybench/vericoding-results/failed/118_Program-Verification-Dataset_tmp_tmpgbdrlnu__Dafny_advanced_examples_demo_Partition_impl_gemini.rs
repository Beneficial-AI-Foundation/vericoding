// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn partition(a: &mut Vec<i32>) -> (r : (usize, usize))
    ensures
        0 <= r.0 && r.0 <= r.1 && r.1 <= a.len(),
        forall|x: int| 0 <= x < r.0 ==> a[x as int] < 0,
        forall|x: int| r.0 <= x < r.1 ==> a[x as int] == 0,
        forall|x: int| r.1 <= x < a.len() ==> a[x as int] > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by changing `(&mut *a).swap(...)` to `a.swap(...)`. */
    let n = a.len();
    let mut p: usize = 0;
    let mut i: usize = 0;
    let mut q: usize = n;

    while i < q
        invariant
            a.len() == n,
            0 <= p && p <= i && i <= q && q <= n,
            forall|x: int| 0 <= x < (p as int) ==> a[x as int] < 0,
            forall|x: int| (p as int) <= x < (i as int) ==> a[x as int] == 0,
            forall|x: int| (q as int) <= x < (n as int) ==> a[x as int] > 0,
        decreases q - i
    {
        if a[i] < 0 {
            a.swap(i, p);
            p = p + 1;
            i = i + 1;
        } else if a[i] == 0 {
            i = i + 1;
        } else {
            q = q - 1;
            a.swap(i, q);
        }
    }

    (p, q)
}
// </vc-code>

}
fn main() {}