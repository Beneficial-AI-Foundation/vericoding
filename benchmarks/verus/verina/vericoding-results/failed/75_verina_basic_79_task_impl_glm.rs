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
    /* code modified by LLM (iteration 5): fixed loop invariants and indexing to handle x>=1, and adjusted initialization */
    let mut m = a[0];
    let mut i = 0usize;

    while i < x
        invariant
            0 <= i <= x,
            (forall |k: int| 0 <= k < (i as int) ==> a[k] <= m),
            (i > 0 ==> (exists |k: int| 0 <= k < (i as int) && a[k] == m))
        decreases (x - i) as int
    {
        if a[i] > m {
            m = a[i];
        }
        i += 1;
    }

    let mut p = a.len() - 1;
    let mut j = x;
    while j < a.len()
        invariant
            x <= j <= a.len(),
            (forall |k: int| (x as int) <= k < (j as int) ==> a[k] <= m),
            (p == a.len() - 1 || (p == j && a[j as int] > m))
        decreases (a.len() - j) as int
    {
        if a[j] > m {
            p = j;
            break;
        }
        j += 1;
    }

    (m, p)
}
// </vc-code>

}
fn main() {}