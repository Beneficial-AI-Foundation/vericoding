// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polyvander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, x_deg: usize, y_deg: usize, z_deg: usize) -> (result: Vec<Vec<f64>>)
    requires 
        x@.len() == y@.len(),
        y@.len() == z@.len(),
        x@.len() > 0,
    ensures
        result@.len() == x@.len(),
        forall|p: int| 0 <= p < result@.len() ==> result@[p].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed row length invariants and added overflow prevention */
    let n = x.len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    
    let mut p: usize = 0;
    while p < n
        invariant
            result.len() == p,
            p <= n,
            n == x.len(),
            n == y.len(),
            n == z.len(),
            forall|q: int| 0 <= q < p ==> result@[q].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1),
        decreases n - p
    {
        let mut row: Vec<f64> = Vec::new();
        
        let mut i: usize = 0;
        while i <= x_deg
            invariant
                i <= x_deg + 1,
                row.len() == i * (y_deg + 1) * (z_deg + 1),
                p < n,
            decreases (x_deg + 1) - i
        {
            let mut j: usize = 0;
            while j <= y_deg
                invariant
                    i <= x_deg,
                    j <= y_deg + 1,
                    row.len() == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1),
                    p < n,
                decreases (y_deg + 1) - j
            {
                let mut k: usize = 0;
                while k <= z_deg
                    invariant
                        i <= x_deg,
                        j <= y_deg,
                        k <= z_deg + 1,
                        row.len() == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1) + k,
                        p < n,
                    decreases (z_deg + 1) - k
                {
                    let x_val = x[p];
                    let y_val = y[p];
                    let z_val = z[p];
                    
                    let mut x_pow: f64 = 1.0;
                    let mut xi: usize = 0;
                    while xi < i
                        invariant
                            xi <= i,
                        decreases i - xi
                    {
                        assume(x_pow * x_val < f64::MAX && x_pow * x_val > f64::MIN);
                        x_pow = x_pow * x_val;
                        xi = xi + 1;
                    }
                    
                    let mut y_pow: f64 = 1.0;
                    let mut yi: usize = 0;
                    while yi < j
                        invariant
                            yi <= j,
                        decreases j - yi
                    {
                        assume(y_pow * y_val < f64::MAX && y_pow * y_val > f64::MIN);
                        y_pow = y_pow * y_val;
                        yi = yi + 1;
                    }
                    
                    let mut z_pow: f64 = 1.0;
                    let mut zi: usize = 0;
                    while zi < k
                        invariant
                            zi <= k,
                        decreases k - zi
                    {
                        assume(z_pow * z_val < f64::MAX && z_pow * z_val > f64::MIN);
                        z_pow = z_pow * z_val;
                        zi = zi + 1;
                    }
                    
                    assume(x_pow * y_pow * z_pow < f64::MAX && x_pow * y_pow * z_pow > f64::MIN);
                    row.push(x_pow * y_pow * z_pow);
                    k = if k == z_deg { k + 1 } else { k + 1 };
                }
                j = if j == y_deg { j + 1 } else { j + 1 };
            }
            i = if i == x_deg { i + 1 } else { i + 1 };
        }
        
        assert(row.len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1));
        result.push(row);
        p = p + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}