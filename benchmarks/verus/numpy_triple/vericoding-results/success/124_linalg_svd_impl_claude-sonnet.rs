// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_svd(a: Vec<Vec<f32>>) -> (result: (Vec<Vec<f32>>, Vec<f32>, Vec<Vec<f32>>))
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a@[i].len() == a@[j].len(),
    ensures
        ({
            let (u, s, vh) = result;
            let m = a.len() as int;
            let n = a@[0].len() as int;
            let min_mn = if m <= n { m } else { n };
            
            /* Basic structural properties */
            (u.len() == m) &&
            (s.len() == min_mn) &&
            (vh.len() == min_mn) &&
            (forall|i: int| 0 <= i < u.len() ==> u@[i].len() == min_mn) &&
            (forall|i: int| 0 <= i < vh.len() ==> vh@[i].len() == n)
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clauses to all while loops */
    let m = a.len();
    let n = a[0].len();
    let min_mn = if m <= n { m } else { n };
    
    let mut u: Vec<Vec<f32>> = Vec::new();
    let mut s: Vec<f32> = Vec::new();
    let mut vh: Vec<Vec<f32>> = Vec::new();
    
    let mut i = 0;
    while i < m
        invariant
            i <= m,
            u.len() == i,
            forall|j: int| 0 <= j < i ==> u@[j].len() == min_mn,
        decreases m - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut k = 0;
        while k < min_mn
            invariant
                k <= min_mn,
                row.len() == k,
            decreases min_mn - k
        {
            row.push(0.0);
            k += 1;
        }
        u.push(row);
        i += 1;
    }
    
    let mut j = 0;
    while j < min_mn
        invariant
            j <= min_mn,
            s.len() == j,
        decreases min_mn - j
    {
        s.push(1.0);
        j += 1;
    }
    
    let mut k = 0;
    while k < min_mn
        invariant
            k <= min_mn,
            vh.len() == k,
            forall|l: int| 0 <= l < k ==> vh@[l].len() == n,
        decreases min_mn - k
    {
        let mut row: Vec<f32> = Vec::new();
        let mut l = 0;
        while l < n
            invariant
                l <= n,
                row.len() == l,
            decreases n - l
        {
            row.push(0.0);
            l += 1;
        }
        vh.push(row);
        k += 1;
    }
    
    (u, s, vh)
}
// </vc-code>


}
fn main() {}