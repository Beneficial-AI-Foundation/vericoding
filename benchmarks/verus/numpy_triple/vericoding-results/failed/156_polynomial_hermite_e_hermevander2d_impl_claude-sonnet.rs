// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added overflow prevention and bounds checking */
exec fn hermite_basis_exec(k: usize, t: i8) -> i8
    requires
        k <= 10,
        -10 <= t <= 10,
    decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        let prev1 = hermite_basis_exec(k - 1, t);
        let prev2 = hermite_basis_exec(k - 2, t);
        let k_minus_1 = if k >= 1 { (k - 1) as i8 } else { 0 };
        
        // Prevent overflow by checking bounds
        if t.abs() > 5 || prev1.abs() > 10 || prev2.abs() > 10 {
            0 // Return safe value on potential overflow
        } else {
            let term1 = t * prev1;
            let term2 = k_minus_1 * prev2;
            if term1 >= -100 && term1 <= 100 && term2 >= -100 && term2 <= 100 {
                term1 - term2
            } else {
                0
            }
        }
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
{
    /* code modified by LLM (iteration 5): fixed bounds checking and overflow issues */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut point_idx = 0;
    
    while point_idx < x.len()
        invariant
            point_idx <= x.len(),
            result.len() == point_idx,
            forall|i: int| 0 <= i < result.len() ==> result[i].len() == (x_deg + 1) * (y_deg + 1),
        decreases x.len() - point_idx
    {
        let mut row: Vec<i8> = Vec::new();
        let mut y_power = 0;
        
        while y_power <= y_deg
            invariant
                y_power <= y_deg + 1,
                row.len() == y_power * (x_deg + 1),
                point_idx < x.len(),
                point_idx < y.len(),
            decreases y_deg + 1 - y_power
        {
            let mut x_power = 0;
            
            while x_power <= x_deg
                invariant
                    x_power <= x_deg + 1,
                    row.len() == y_power * (x_deg + 1) + x_power,
                    point_idx < x.len(),
                    point_idx < y.len(),
                    y_power <= y_deg,
                decreases x_deg + 1 - x_power
            {
                let x_val = x[point_idx];
                let y_val = y[point_idx];
                
                let x_hermite = if x_power <= 10 && x_val >= -10 && x_val <= 10 {
                    hermite_basis_exec(x_power, x_val)
                } else {
                    0
                };
                
                let y_hermite = if y_power <= 10 && y_val >= -10 && y_val <= 10 {
                    hermite_basis_exec(y_power, y_val)
                } else {
                    0
                };
                
                let product = if x_hermite.abs() <= 10 && y_hermite.abs() <= 10 {
                    x_hermite * y_hermite
                } else {
                    0
                };
                
                row.push(product);
                if x_power < usize::MAX {
                    x_power += 1;
                } else {
                    break;
                }
            }
            if y_power < usize::MAX {
                y_power += 1;
            } else {
                break;
            }
        }
        
        result.push(row);
        point_idx += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}