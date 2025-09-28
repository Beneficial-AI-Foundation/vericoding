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
/* code modified by LLM (iteration 5): Fixed `reserve_with_capacity` to `reserve_exact` and iterators, adjusted loop bounds and indices. */
{
    let n = pol.len();
    let mut a: Vec<f64> = Vec::new();
    a.reserve_exact(n);

    let mut d: Vec<f64> = Vec::new();
    d.reserve_exact(n);

    for i in 0..n {
        a.push(0.0);
        d.push(0.0);
    }

    if n > 0 {
        let mut i_verifier: usize = n;
        while i_verifier > 0
            invariant
                n == pol.len(),
                n == a.len(),
                n == d.len(),
                0 <= i_verifier && i_verifier <= n,
                // All elements from `i_verifier` to `n-1` are processed and correct relative to current `d` and `pol`
            decreases i_verifier
        {
            i_verifier = i_verifier - 1;
            let i = i_verifier;
            
            d.set(i, pol[i] + d[i]);

            if i >= 2 {
                d.set(i - 2, d[i - 2] - d[i]);
            }
        }

        if n >= 2 {
            a.set(0, (d[0] - d[2]) / 2.0);
            a.set(1, d[1]);

            let mut k_verifier: usize = 2;
            while k_verifier < n
                invariant
                    n == a.len(),
                    n == d.len(),
                    2 <= k_verifier && k_verifier <= n,
                    // All elements from 2 to `k_verifier-1` of `a` are correctly set
                decreases (n - k_verifier)
            {
                let k = k_verifier;
                a.set(k, d[k]);
                k_verifier = k_verifier + 1;
            }
        } else if n == 1 {
            a.set(0, d[0]);
        }
    }

    a
}
// </vc-code>

}
fn main() {}