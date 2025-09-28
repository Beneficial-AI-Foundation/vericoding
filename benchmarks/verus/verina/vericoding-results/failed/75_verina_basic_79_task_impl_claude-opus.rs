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
    /* code modified by LLM (iteration 5): Added decreases clauses to all while loops for termination proof */
    let mut m = a[0];
    let mut p = x;
    let mut i = 0;
    
    while i < x
        invariant
            0 <= i <= x,
            i <= p,
            p <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] <= m,
            exists|j: int| 0 <= j < i && a[j] == m,
            p == i || p == a.len() - 1,
            p == a.len() - 1 ==> (forall|j: int| i <= j < a.len() ==> a[j] <= m),
        decreases x - i
    {
        if a[i as usize] > m {
            m = a[i as usize];
            p = i;
        }
        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j < x ==> a[j] <= m);
    assert(exists|j: int| 0 <= j < x && a[j] == m);
    
    if p < a.len() - 1 {
        let mut j = x;
        while j <= p
            invariant
                x <= j <= p + 1,
                p < a.len() - 1,
                forall|k: int| 0 <= k < x ==> a[k] <= m,
                exists|k: int| 0 <= k < x && a[k] == m,
            decreases p + 1 - j
        {
            if a[j as usize] > m {
                assert(x <= j && j <= p && a[j as int] > m);
                assert(exists|k: int| x <= k <= p && a[k] > m);
                return (m, p);
            }
            j = j + 1;
        }
    }
    
    if p == x {
        let mut found = false;
        let mut k = x;
        while k < a.len()
            invariant
                x <= k <= a.len(),
                forall|j: int| 0 <= j < x ==> a[j] <= m,
                exists|j: int| 0 <= j < x && a[j] == m,
                !found ==> (forall|j: int| x <= j < k ==> a[j] <= m),
                found ==> (exists|j: int| x <= j < a.len() && a[j] > m),
                found ==> p < a.len() - 1,
            decreases a.len() - k
        {
            if a[k as usize] > m {
                p = k;
                found = true;
                break;
            }
            k = k + 1;
        }
        
        if !found {
            p = a.len() - 1;
        }
    }
    
    (m, p)
}
// </vc-code>

}
fn main() {}