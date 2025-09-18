// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): basic max and predicate for prefix maximums */
fn max_i32(a: i32, b: i32) -> i32 { if a >= b { a } else { b } }

/* helper modified by LLM (iteration 3): predicate states m is the maximum among first n elements */
spec fn is_prefix_max(a: Seq<i32>, n: nat, m: i32) -> bool {
    (forall|i: int| 0 <= i < n as int ==> a[i] <= m)
    && (exists|i: int| 0 <= i < n as int && a[i] == m)
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
    /* code modified by LLM (iteration 3): removed commas after invariants; two-pass scan to compute prefix max and first exceedance */
    let n = a.len();
    if x == 0 {
        let m = a[0];
        let p = n - 1;
        return (m, p);
    }

    let mut m: i32 = a[0];
    let mut j: usize = 0;
    let mut i: usize = 1;
    while i < x
        invariant n == a.len()
        invariant 1 <= i && i <= x
        invariant j < i
        invariant m == a[j]
        invariant forall|k: int| 0 <= k < i as int ==> a@[k] <= m
        decreases x - i
    {
        if a[i] > m {
            m = a[i];
            j = i;
        }
        i += 1;
    }

    let mut p: usize = n - 1;
    let mut found: bool = false;
    let mut t: usize = x;
    while t < n
        invariant n == a.len()
        invariant x <= t && t <= n
        invariant x <= p && p < n
        invariant !found ==> forall|k: int| x as int <= k < t as int ==> a@[k] <= m
        invariant found ==> x <= p && p < t && a[p] > m
        decreases n - t
    {
        if a[t] > m {
            p = t;
            found = true;
            break;
        }
        t += 1;
    }

    (m, p)
}
// </vc-code>

}
fn main() {}