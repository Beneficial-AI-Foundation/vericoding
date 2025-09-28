// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added overflow protection and bounds validation */
fn compute_vandermonde_entry(x: f64, y: f64, z: f64, i: usize, j: usize, k: usize, x_deg: usize, y_deg: usize, z_deg: usize) -> f64
    requires
        i <= x_deg,
        j <= y_deg,
        k <= z_deg,
        x_deg < usize::MAX,
        y_deg < usize::MAX,
        z_deg < usize::MAX,
{
    let mut x_power = 1.0;
    let mut y_power = 1.0;
    let mut z_power = 1.0;
    
    for idx in 0..i {
        x_power = x_power * x;
    }
    
    for idx in 0..j {
        y_power = y_power * y;
    }
    
    for idx in 0..k {
        z_power = z_power * z;
    }
    
    x_power * y_power * z_power
}
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
/* code modified by LLM (iteration 4): added overflow checks and loop invariants */
{
    let mut result = Vec::with_capacity(x.len());
    
    for p in 0..x.len()
        invariant
            0 <= p <= x@.len(),
            result@.len() == p,
        decreases (x@.len() - p)
    {
        assert(p < x@.len() && p < y@.len() && p < z@.len());
        
        let x_safe = x_deg < usize::MAX;
        let y_safe = y_deg < usize::MAX;
        let z_safe = z_deg < usize::MAX;
        
        assert(x_safe && y_safe && z_safe);
        
        let x_size = x_deg + 1;
        let y_size = y_deg + 1;
        let z_size = z_deg + 1;
        
        assert(x_size > 0 && y_size > 0 && z_size > 0);
        
        let expected_entries = x_size * y_size * z_size;
        let mut row = Vec::with_capacity(expected_entries);
        
        for i in 0..x_size {
            for j in 0..y_size {
                for k in 0..z_size {
                    let entry = compute_vandermonde_entry(x[p], y[p], z[p], i, j, k, x_deg, y_deg, z_deg);
                    row.push(entry);
                }
            }
        }
        
        assert(row@.len() == expected_entries);
        result.push(row);
    }
    
    result
}
// </vc-code>

}
fn main() {}