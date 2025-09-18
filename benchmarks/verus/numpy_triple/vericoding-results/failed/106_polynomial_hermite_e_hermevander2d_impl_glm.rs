// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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

fn hermevander2d(x: Vec<i32>, y: Vec<i32>, x_deg: usize, y_deg: usize) -> (result: Vec<Vec<i32>>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|point_idx: int| 0 <= point_idx < result.len() ==> 
            result[point_idx].len() == (x_deg + 1) * (y_deg + 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed overflow and indexing issues */
{
        let n = x.len();
        let mut result = Vec::with_capacity(n);

        for i in 0..n {
            // Assert that i is within bounds for x and y
            assert(i < x.len());
            assert(i < y.len());
            let xi = x[i] as i64;
            let yi = y[i] as i64;

            // Pre-allocate hx and hy with zeros
            let mut hx = vec![0i64; x_deg + 1];
            hx[0] = 1;
            if x_deg >= 1 {
                hx[1] = xi;
            }
            for deg in 2..=x_deg {
                // Use i128 for intermediate calculation to avoid overflow
                let term1 = (xi as i128) * (hx[deg-1] as i128);
                let term2 = ((deg-1) as i128) * (hx[deg-2] as i128);
                let h_val = term1 - term2;
                // Assert that the result is within i64 range
                assert(h_val >= i64::MIN as i128 && h_val <= i64::MAX as i128);
                hx[deg] = h_val as i64;
            }

            let mut hy = vec![0i64; y_deg + 1];
            hy[0] = 1;
            if y_deg >= 1 {
                hy[1] = yi;
            }
            for deg in 2..=y_deg {
                let term1 = (yi as i128) * (hy[deg-1] as i128);
                let term2 = ((deg-1) as i128) * (hy[deg-2] as i128);
                let h_val = term1 - term2;
                assert(h_val >= i64::MIN as i128 && h_val <= i64::MAX as i128);
                hy[deg] = h_val as i64;
            }

            let mut row = Vec::new();
            for j in 0..=x_deg {
                for k in 0..=y_deg {
                    let product = hx[j] * hy[k];
                    // Assert that the product is within i32 range
                    assert(product >= i32::MIN as i64 && product <= i32::MAX as i64);
                    row.push(product as i32);
                }
            }
            result.push(row);
        }

        result
    }
// </vc-code>

}
fn main() {}