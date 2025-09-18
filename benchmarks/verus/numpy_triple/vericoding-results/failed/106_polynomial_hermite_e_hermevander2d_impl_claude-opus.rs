// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added trigger annotation to fix quantifier inference */
proof fn hermite_basis_computable(k: nat, t: int)
    ensures 
        #[trigger] hermite_basis(k, t) == hermite_basis(k, t)
    decreases k
{
    if k == 0 {
    } else if k == 1 {
    } else {
        hermite_basis_computable((k - 1) as nat, t);
        hermite_basis_computable((k - 2) as nat, t);
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
{
    /* code modified by LLM (iteration 5): no changes needed, kept existing implementation */
    let mut result: Vec<Vec<i32>> = Vec::new();
    let n_points = x.len();
    
    let mut point_idx: usize = 0;
    while point_idx < n_points
        invariant
            point_idx <= n_points,
            result.len() == point_idx,
            forall|i: int| 0 <= i < point_idx ==> result[i].len() == (x_deg + 1) * (y_deg + 1)
        decreases n_points - point_idx
    {
        let x_val = x[point_idx];
        let y_val = y[point_idx];
        
        let mut row: Vec<i32> = Vec::new();
        
        let mut j: usize = 0;
        while j <= y_deg
            invariant
                j <= y_deg + 1,
                row.len() == j * (x_deg + 1)
            decreases y_deg + 1 - j
        {
            let mut i: usize = 0;
            while i <= x_deg
                invariant
                    i <= x_deg + 1,
                    row.len() == j * (x_deg + 1) + i
                decreases x_deg + 1 - i
            {
                proof {
                    hermite_basis_computable(i as nat, x_val as int);
                    hermite_basis_computable(j as nat, y_val as int);
                }
                
                let h_x = if i == 0 {
                    1i32
                } else if i == 1 {
                    x_val
                } else {
                    let mut k: usize = 2;
                    let mut h_k_minus_2 = 1i32;
                    let mut h_k_minus_1 = x_val;
                    while k <= i
                        invariant
                            2 <= k <= i + 1
                        decreases i + 1 - k
                    {
                        let h_k = x_val * h_k_minus_1 - (k - 1) as i32 * h_k_minus_2;
                        h_k_minus_2 = h_k_minus_1;
                        h_k_minus_1 = h_k;
                        k = k + 1;
                    }
                    h_k_minus_1
                };
                
                let h_y = if j == 0 {
                    1i32
                } else if j == 1 {
                    y_val
                } else {
                    let mut k: usize = 2;
                    let mut h_k_minus_2 = 1i32;
                    let mut h_k_minus_1 = y_val;
                    while k <= j
                        invariant
                            2 <= k <= j + 1
                        decreases j + 1 - k
                    {
                        let h_k = y_val * h_k_minus_1 - (k - 1) as i32 * h_k_minus_2;
                        h_k_minus_2 = h_k_minus_1;
                        h_k_minus_1 = h_k;
                        k = k + 1;
                    }
                    h_k_minus_1
                };
                
                row.push(h_x * h_y);
                i = i + 1;
            }
            j = j + 1;
        }
        
        result.push(row);
        point_idx = point_idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}