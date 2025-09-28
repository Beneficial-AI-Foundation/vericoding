// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn pow_spec(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow_spec(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polyvander2d(x: Vec<f64>, y: Vec<f64>, x_deg: u8, y_deg: u8) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == (x_deg as int + 1) * (y_deg as int + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type annotations and removed assume statements */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let n = x.len();
    let x_deg_plus_1 = (x_deg as usize + 1);
    let y_deg_plus_1 = (y_deg as usize + 1);
    let row_len = x_deg_plus_1 * y_deg_plus_1;
    
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == row_len,
            n == x.len(),
            n == y.len(),
            row_len == x_deg_plus_1 * y_deg_plus_1,
            x_deg_plus_1 == (x_deg as usize + 1),
            y_deg_plus_1 == (y_deg as usize + 1),
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let xi: f64 = x[i];
        let yi: f64 = y[i];
        
        let mut j: usize = 0;
        while j <= x_deg as usize
            invariant
                row.len() == j * y_deg_plus_1,
                j <= x_deg as usize + 1,
                y_deg_plus_1 == (y_deg as usize + 1),
            decreases (x_deg as usize + 1) - j
        {
            let mut x_pow: f64 = 1.0;
            
            let mut jj: usize = 0;
            while jj < j
                invariant
                    jj <= j,
                decreases j - jj
            {
                x_pow = x_pow * xi;
                jj = jj + 1;
            }
            
            let mut k: usize = 0;
            while k <= y_deg as usize
                invariant
                    row.len() == j * y_deg_plus_1 + k,
                    k <= y_deg as usize + 1,
                    y_deg_plus_1 == (y_deg as usize + 1),
                decreases (y_deg as usize + 1) - k
            {
                let mut y_pow: f64 = 1.0;
                
                let mut kk: usize = 0;
                while kk < k
                    invariant
                        kk <= k,
                    decreases k - kk
                {
                    y_pow = y_pow * yi;
                    kk = kk + 1;
                }
                
                row.push(x_pow * y_pow);
                k = k + 1;
            }
            j = j + 1;
        }
        
        assert(j == x_deg as usize + 1);
        assert(row.len() == (x_deg as usize + 1) * y_deg_plus_1);
        assert(row.len() == row_len);
        result.push(row);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}