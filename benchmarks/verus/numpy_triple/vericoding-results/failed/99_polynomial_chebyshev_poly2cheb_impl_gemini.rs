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
    /* code modified by LLM (iteration 5): added assertions and invariants to guide the verifier in proving index safety. */
    let n = pol.len();
    
    let mut c = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            c.len() == i,
            i <= n,
            pol.len() == n,
        decreases n - i,
    {
        c.push(0.0);
        i = i + 1;
    }

    let mut j: usize = n;
    while j > 0
        invariant
            pol.len() == n,
            c.len() == n,
            j <= n,
        decreases j,
    {
        j = j - 1;

        let c_next = c.clone();
        assert(c_next.len() == n);
        let pol_j = pol[j];

        let c_curr_0 = pol_j + if n > 1 {
            assert(1 < c_next.len());
            c_next[1] / 2.0
        } else { 0.0 };
        c.set(0, c_curr_0);

        if n > 1 {
            assert(0 < c_next.len());
            let c_curr_1 = c_next[0] + if n > 2 {
                assert(2 < c_next.len());
                c_next[2] / 2.0
            } else { 0.0 };
            c.set(1, c_curr_1);
        }

        let mut k: usize = 2;
        while k < n
            invariant
                pol.len() == n,
                c.len() == n,
                c_next.len() == n,
                j < n,
                2 <= k <= n,
            decreases n - k,
        {
            assert(k - 1 < c_next.len());
            let c_prev_term = c_next[k-1];
            let c_next_term = if k + 1 < n {
                assert(k + 1 < c_next.len());
                c_next[k+1]
            } else { 0.0 };
            let c_curr_k = (c_prev_term + c_next_term) / 2.0;
            c.set(k, c_curr_k);
            k = k + 1;
        }
    }
    c
}

// </vc-code>

}
fn main() {}