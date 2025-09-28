// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): safe polynomial multiplication using int arithmetic for proofs */
fn poly_mul(a: Vec<f64>, b: Vec<f64>) -> (result: Vec<f64>)
    requires
        a.len() > 0,
        b.len() > 0,
    ensures
        result.len() == a.len() + b.len() - 1,
{
    let alen = a.len();
    let blen = b.len();
    let alen_i: int = alen as int;
    let blen_i: int = blen as int;
    let n_i: int = alen_i + blen_i - 1;
    proof { assert(n_i >= 1); }
    let n: usize = n_i as usize;

    let mut res: Vec<f64> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            res.len() == k,
        decreases n - k
    {
        res.push(0.0);
        k += 1;
    }

    let mut i: usize = 0;
    while i < alen
        invariant
            i <= alen,
            res.len() == n,
        decreases alen - i
    {
        let mut j: usize = 0;
        while j < blen
            invariant
                j <= blen,
                res.len() == n,
            decreases blen - j
        {
            let idx = i + j;
            proof {
                let ii: int = i as int;
                let jj: int = j as int;
                assert(ii >= 0);
                assert(jj >= 0);
                assert(ii <= alen_i - 1);
                assert(jj <= blen_i - 1);
                assert(ii + jj <= (alen_i - 1) + (blen_i - 1));
                assert(ii + jj < n_i);
            }
            let ai = a[i];
            let bj = b[j];
            let old = res[idx];
            res[idx] = old + ai * bj;
            j += 1;
        }
        i += 1;
    }

    res
}

// </vc-helpers>

// <vc-spec>
fn hermepow(c: Vec<f64>, pow: u8, maxpower: u8) -> (result: Vec<f64>)
    requires 
        pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures

        pow == 0 ==> result.len() == 1 && result[0] == 1.0 && 
            (forall|i: int| 1 <= i < result.len() ==> result[i] == 0.0),
        pow == 1 ==> result.len() == c.len() &&
            (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),

        pow as int >= 1 ==> result.len() == 1 + (c.len() - 1) * pow as int,

        pow as int >= 1 && c.len() > 0 ==> result.len() > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative multiply c pow times using poly_mul with proofs */
    if pow == 0 {
        let mut res: Vec<f64> = Vec::new();
        res.push(1.0);
        res
    } else if pow == 1 {
        c.clone()
    } else {
        let mut res = c.clone();
        let target: usize = pow as usize;
        proof { assert(c.len() > 0); }
        let mut i: usize = 1;
        while i < target
            invariant
                1 <= i,
                i <= target,
                res.len() == 1 + (c.len() - 1) * i,
                res.len() > 0,
            decreases target - i
        {
            proof {
                assert(res.len() > 0);
                assert(c.len() > 0);
            }
            let old_len = res.len();
            res = poly_mul(res, c.clone());
            proof {
                assert(old_len > 0);
                assert(res.len() == old_len + c.len() - 1);
                assert(res.len() == 1 + (c.len() - 1) * (i + 1));
            }
            i += 1;
        }
        res
    }
}

// </vc-code>

}
fn main() {}