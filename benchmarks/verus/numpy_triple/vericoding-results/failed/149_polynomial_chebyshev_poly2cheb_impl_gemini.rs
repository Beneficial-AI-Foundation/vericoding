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
    /* code modified by LLM (iteration 5): [fixed compilation error by initializing Vec with a loop] */
    let n = pol.len();
    let mut c: Vec<f64> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            c.len() == j,
            j <= n,
            pol.len() == n,
        decreases n - j
    {
        c.push(0.0);
        j = j + 1;
    }

    let mut i = n;
    while i > 0
        invariant
            0 < i && i <= n,
            pol.len() == n,
            c.len() == n,
        decreases i
    {
        i = i - 1;
        let p_i = pol[i];

        if n > 1 {
            let c_old = c.clone();

            c.set(0, c_old[1] / 2.0);
            
            let c_old_2 = if n > 2 { c_old[2] } else { 0.0 };
            c.set(1, c_old[0] + c_old_2 / 2.0);
            
            let mut k: usize = 2;
            while k < n
                invariant
                    2 <= k && k <= n,
                    c.len() == n,
                    c_old.len() == n,
                    pol.len() == n,
                decreases n - k
            {
                let c_old_k_minus_1 = c_old[k - 1];
                let c_old_k_plus_1 = if k + 1 < n { c_old[k + 1] } else { 0.0 };
                c.set(k, (c_old_k_minus_1 + c_old_k_plus_1) / 2.0);
                k = k + 1;
            }
        }

        let new_c0 = c[0] + p_i;
        c.set(0, new_c0);
    }
    
    c
}
// </vc-code>

}
fn main() {}