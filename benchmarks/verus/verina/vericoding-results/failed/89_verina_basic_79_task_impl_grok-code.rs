// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added explicit type annotation to result in ensures clause to fix compilation error */
fn find_max(a: &Vec<i32>, start: usize, end: usize) -> i32
    requires
        start <= end && end <= a.len(),
    ensures (|result: i32|) {
        (forall |i: int| start as int <= i < end as int ==> a@[i] <= result)
        && if start < end { exists |i: int| start as int <= i < end as int && a@[i] == result } else { true }
    }
{
    if start == end {
        i32::MIN
    } else {
        let mut m = a[start];
        let mut i = start + 1;
        while i < end
            invariant
                start as int <= end as int && end as int <= a.len() as int,
                start as int + 1 <= i as int <= end as int,
                a@[start as int] <= m,
                (forall |k: int| start as int + 1 <= k < i as int ==> a@[k] <= m),
                (forall |k: int| start as int <= k < i as int ==> a@[k] <= m)
        {
            if a[i] > m {
                m = a[i];
            }
            i += 1;
        }
        m
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
/* code modified by LLM (iteration 5): implemented the method body to compute online max without verification bypasses */
{
    let m = find_max(a, 0, x);
    let mut p = a.len() - 1;
    let mut found = false;
    let mut i = x;
    while i < a.len()
        invariant
            x as int <= i as int <= a.len() as int,
            (forall |j: int| x as int <= j < i as int ==> a@[j] <= m),
            !found || (exists |j: int| x as int <= j <= p as int && a@[j] > m)
    {
        if a[i] > m {
            p = i;
            found = true;
        }
        i += 1;
    }
    (m, p)
}
// </vc-code>

}
fn main() {}