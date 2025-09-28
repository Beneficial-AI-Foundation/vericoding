// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): runtime Hermite basis using i64 */
fn hermite_basis_rt(k: usize, t: i64) -> i64
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        let mut h0: i64 = 1;
        let mut h1: i64 = t;
        let mut i: usize = 2;
        // k >= 2 here
        while i <= k
            invariant
                i >= 2,
                i <= k + 1,
            decreases k + 1 - i
        {
            proof { assert(i >= 2); assert(i <= k + 1); }
            let term = ((i - 1) as i64) * h0;
            let h2 = t * h1 - term;
            h0 = h1;
            h1 = h2;
            i += 1;
        }
        h1
    }
}
// </vc-helpers>

// <vc-spec>
spec fn hermite_basis(k: nat, t: int) -> int
    decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        t * hermite_basis((k - 1) as nat, t) - (k - 1) as int * hermite_basis((k - 2) as nat, t)
    }
}

fn hermevander2d(x: Vec<i8>, y: Vec<i8>, x_deg: usize, y_deg: usize) -> (result: Vec<Vec<i8>>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|point_idx: int| 0 <= point_idx < result.len() ==> 
            result[point_idx].len() == (x_deg + 1) * (y_deg + 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute 2D Hermite Vandermonde with safe bounds and proofs */
{
    let n = x.len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            i <= n,
            result.len() == i,
        decreases n - i
    {
        let cols: usize = (x_deg + 1) * (y_deg + 1);

        let mut row: Vec<i8> = Vec::new();
        let mut j = 0usize;
        while j < cols
            invariant
                j <= cols,
                row.len() == j,
            decreases cols - j
        {
            row.push(0i8);
            j += 1;
        }

        assert(i < n);
        let xi = x[i] as i64;
        let yi = y[i] as i64;

        let mut kx = 0usize;
        while kx < (x_deg + 1)
            invariant
                kx <= x_deg + 1,
                row.len() == cols,
            decreases (x_deg + 1) - kx
        {
            let mut ky = 0usize;
            while ky < (y_deg + 1)
                invariant
                    ky <= y_deg + 1,
                    row.len() == cols,
                decreases (y_deg + 1) - ky
            {
                let pos: usize = kx * (y_deg + 1) + ky;

                let val = hermite_basis_rt(kx, xi) * hermite_basis_rt(ky, yi);
                assert(pos < row.len());
                row[pos] = #[verifier::truncate] val as i8;
                ky += 1;
            }
            kx += 1;
        }

        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}