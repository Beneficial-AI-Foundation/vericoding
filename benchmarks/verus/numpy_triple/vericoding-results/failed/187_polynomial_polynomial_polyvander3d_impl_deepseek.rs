// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn polyvander_1d(x: Vec<f64>, deg: usize) -> (v: Vec<Vec<f64>>)
    requires
        x@.len() > 0,
        deg >= 0,
    ensures
        v@.len() == x@.len(),
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@[i].len() ==> v@[i][j] == (if j == 0 { 1.0 } else { x@[i].powi(j as i32) }),
{
    let n = x@.len() as usize;
    let m = deg + 1;
    let mut result: Vec<Vec<f64>> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result@.len() == i,
            forall|p: int| 0 <= p < i ==> result@[p].len() == m,
            forall|p: int, q: int| 0 <= p < i && 0 <= q < m ==> result@[p][q] == (if q == 0 { 1.0 } else { x@[p].powi(q as i32) }),
    {
        let mut row: Vec<f64> = Vec::with_capacity(m);
        let mut j: usize = 0;
        while j < m
            invariant
                j <= m,
                row@.len() == j,
                forall|k: int| 0 <= k < j ==> row@[k] == (if k == 0 { 1.0 } else { x@[i].powi(k as i32) }),
        {
            let power = if j == 0 { 1.0 } else { x@[i].powi(j as i32) };
            row.push(power);
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
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
{
    /* code modified by LLM (iteration 5): fixed sequence indexing by removing unnecessary as int casts */
    let n = x@.len() as usize;
    let mut result: Vec<Vec<f64>> = Vec::with_capacity(n);
    let mut idx: usize = 0;
    
    while idx < n
        invariant
            idx <= n,
            result@.len() == idx,
            forall|p: int| 0 <= p < idx ==> result@[p].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1),
    {
        let mut row: Vec<f64> = Vec::with_capacity((x_deg + 1) * (y_deg + 1) * (z_deg + 1));
        let mut i: usize = 0;
        
        while i <= x_deg
            invariant
                i <= x_deg + 1,
                row@.len() == i * (y_deg + 1) * (z_deg + 1),
        {
            let mut j: usize = 0;
            
            while j <= y_deg
                invariant
                    j <= y_deg + 1,
                    row@.len() == (i * (y_deg + 1) * (z_deg + 1)) + (j * (z_deg + 1)),
            {
                let mut k: usize = 0;
                
                while k <= z_deg
                    invariant
                        k <= z_deg + 1,
                        row@.len() == (i * (y_deg + 1) * (z_deg + 1)) + (j * (z_deg + 1)) + k,
                {
                    let x_power = if i == 0 { 1.0 } else { x@[idx].powi(i as i32) };
                    let y_power = if j == 0 { 1.0 } else { y@[idx].powi(j as i32) };
                    let z_power = if k == 0 { 1.0 } else { z@[idx].powi(k as i32) };
                    let product = x_power * y_power * z_power;
                    row.push(product);
                    k = k + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        
        result.push(row);
        idx = idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}