// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute prefix maximum and its index for first x elements */
spec fn prefix_max(a: &Vec<i32>, x: nat) -> (i32, nat)
    requires x > 0 && x <= a.len()
    ensures ({ let (m, idx) = result; idx < x && a@[idx] == m && (forall|i: nat| i < x ==> a@[i] <= m) })
    decreases x {
    if x == 1 {
        (a@[0], 0)
    } else {
        let (m_prev, idx_prev) = prefix_max(a, x - 1);
        let cur = a@[(x - 1)];
        if cur > m_prev {
            (cur, x - 1)
        } else {
            (m_prev, idx_prev)
        }
    }
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
    /* code modified by LLM (iteration 5): compute prefix max using helper and scan for first index >= x with element > m */
    let (m, _idx) = if x == 0 {
        (a@[(0)], 0)
    } else {
        prefix_max(a, x as nat)
    };
    let mut p: usize = x;
    while p < a.len()
        invariant x <= p && p <= a.len()
        invariant forall|k: nat| k < x as nat ==> a@[k] <= m
        decreases (a.len() - p)
    {
        if a@[p] > m {
            break;
        }
        p += 1;
    }
    if p >= a.len() {
        (m, a.len() - 1)
    } else {
        (m, p)
    }
}
// </vc-code>

}
fn main() {}