// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): computes max of prefix [0,x) */
fn compute_prefix_max(a: &Vec<i32>, x: usize) -> (result: i32)
    requires
        a.len() > 0,
        x > 0,
        x <= a.len(),
    ensures
        forall|i: int| 0 <= i < x ==> a@[i] <= result,
        exists|i: int| 0 <= i < x && a@[i] == result,
{
    let mut m: i32 = a[0];
    let mut i: usize = 1;
    while i < x
        invariant
            1 <= i,
            i <= x,
            forall|k: int| 0 <= k < i ==> a@[k] <= m,
            exists|k: int| 0 <= k < i && a@[k] == m,
        decreases
            x - i
    {
        if a[i] > m {
            m = a[i];
        }
        i += 1;
    }
    let result = m;
    result
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
    /* code modified by LLM (iteration 5): compute prefix max and find first later element greater than it */
    let len = a.len();
    let mut m: i32 = a[0];
    if x > 0 {
        m = compute_prefix_max(a, x);
    }
    let mut p: usize = len - 1;
    let mut j: usize = x;
    while j < len
        invariant
            x <= j,
            j <= len,
        decreases
            len - j
    {
        if a[j] > m {
            p = j;
            j = len;
        } else {
            j += 1;
        }
    }
    (m, p)
}
// </vc-code>

}
fn main() {}