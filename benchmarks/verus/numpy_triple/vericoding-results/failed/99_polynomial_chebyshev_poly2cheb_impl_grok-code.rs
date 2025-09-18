// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn poly2cheb(pol: Vec<f64>) -> (result: Vec<f64>)
    requires pol.len() > 0,
    ensures 
        result.len() == pol.len(),

        (pol.len() == 4 && pol[0] == 0.0 && pol[1] == 1.0 && pol[2] == 2.0 && pol[3] == 3.0) ==>
            (result[0] == 1.0 && result[1] == 3.25 && result[2] == 1.0 && result[3] == 0.75),

        (pol.len() == 3 && pol[0] == 0.0 && pol[1] == 0.0 && pol[2] == 1.0) ==>
            (result[0] == 0.5 && result[1] == 0.0 && result[2] == 0.5),

        (pol.len() == 4 && pol[0] == 0.0 && pol[1] == 0.0 && pol[2] == 0.0 && pol[3] == 1.0) ==>
            (result[0] == 0.0 && result[1] == 0.75 && result[2] == 0.0 && result[3] == 0.25)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): replaced compound assignment with explicit addition to fix compilation error */
    let n = pol.len();
    let mut t_coeffs: Vec<Vec<f64>> = Vec::with_capacity(n);
    if n > 0 {
        let mut t0 = vec![0.0; n];
        t0[0] = 1.0;
        t_coeffs.push(t0);
    }
    if n > 1 {
        let mut t1 = vec![0.0; n];
        t1[1] = 1.0;
        t_coeffs.push(t1);
    }
    let mut k = 2;
    while k < n
        invariant
            t_coeffs.len() == (if k > 2 { k } else { if n > 1 { 2 } else if n > 0 { 1 } else { 0 } }),
            &&& forall|i: int| 0 <= i < t_coeffs.len() ==> t_coeffs[i].len() == n,
        decreases n - k,
    {
        let mut tk = vec![0.0; n];
        let mut j = 0;
        while j < n
            invariant
                forall|jj: int| 0 <= jj < j ==> (k as isize - 2) >= 0 ==> tk[jj] == -t_coeffs@[k-2][jj],
                &&& forall|jj: int| 0 <= jj < j ==> jj > 0 ==> tk[jj] == 2.0 * t_coeffs@[k-1][jj-1],
            decreases n - j,
        {
            if (k as isize - 2) >= 0 {
                tk[j] = -t_coeffs@[k-2][j];
            }
            if j > 0 {
                tk[j] = tk[j] + 2.0 * t_coeffs@[k-1][j-1];
            }
            j += 1;
        }
        t_coeffs.push(tk);
        k += 1;
    }
    let mut c = vec![0.0; n];
    let mut i = (n-1) as isize;
    while i >= 0
        invariant
            forall|ii: int| 0 <= ii < n ==> (i > (ii as isize)) ==> c@[ii] == polynomial_evaluation(...),
            &&& c@[0..n]
        decreases i + 1,
    {
        let k = i as usize;
        let mut sum = 0.0;
        let mut j = 0;
        while j < k
            invariant
                sum == polynomial_sum(j, ...),
            decreases k - j,
        {
            sum = sum + t_coeffs@[j][k] * c@[j];
            j += 1;
        }
        c[k] = (pol@[k] - sum) / t_coeffs@[k][k];
        i -= 1;
    }
    c
}
// </vc-code>

}
fn main() {}