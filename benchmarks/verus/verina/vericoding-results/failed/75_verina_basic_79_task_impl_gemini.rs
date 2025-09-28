// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed spec indexing and added type casts */
fn find_max_prefix(a: &Vec<i32>, x: usize) -> (max_val: i32)
    requires
        0 < x <= a.len(),
    ensures
        (exists|i: int| 0 <= i < (x as int) && a[i] == max_val),
        (forall|i: int| 0 <= i < (x as int) ==> a[i] <= max_val),
{
    let mut max_val = a[0];
    let mut i: usize = 1;
    while i < x
        invariant
            0 < x <= a.len(),
            1 <= i <= x,
            (exists|k: int| 0 <= k < (i as int) && a[k] == max_val),
            (forall|k: int| 0 <= k < (i as int) ==> a[k] <= max_val),
        decreases x - i
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i = i + 1;
    }
    max_val
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
{
    /* code modified by LLM (iteration 2): fixed spec indexing and added type casts */
    if x == 0 {
        // This path is designed to fail verification. The spec is unsatisfiable for x=0,
        // because (exists|i: int| 0 <= i < 0 && ...) is always false.
        return (0, 0);
    }

    let m = find_max_prefix(a, x);

    let mut p: usize = x;
    while p < a.len()
        invariant
            a.len() > 0,
            0 < x < a.len(),
            x <= p <= a.len(),
            (exists|i: int| 0 <= i < (x as int) && a[i] == m),
            (forall|i: int| 0 <= i < (x as int) ==> a[i] <= m),
            (forall|k: int| (x as int) <= k < (p as int) ==> a[k] <= m),
        decreases a.len() - p
    {
        if a[p] > m {
            return (m, p);
        }
        p = p + 1;
    }

    assert(forall|k: int| (x as int) <= k < (a.len() as int) ==> a[k] <= m);
    return (m, a.len() - 1);
}
// </vc-code>

}
fn main() {}