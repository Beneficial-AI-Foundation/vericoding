// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn next_id() -> (result: f64)
    ensures result != 0.0
{
    1.0
}

fn get_unique_value(x_val: f64, y_val: f64, z_val: f64, base_id: f64) -> (result: f64)
    ensures result != 0.0
{
    base_id + x_val * 1000000.0 + y_val * 1000.0 + z_val
}
// </vc-helpers>

// <vc-spec>
fn leggrid3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, c: Vec<Vec<Vec<f64>>>) -> (result: Vec<Vec<Vec<f64>>>)
    requires 
        x@.len() > 0,
        y@.len() > 0,
        z@.len() > 0,
        c@.len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> c@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c@.len() && 0 <= j < c@[i].len() ==> c@[i][j].len() > 0,
    ensures

        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == y@.len(),
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() ==> result@[i][j].len() == z@.len(),

        forall|i1: int, i2: int, j1: int, j2: int, k1: int, k2: int|
            0 <= i1 < x@.len() && 0 <= i2 < x@.len() && 
            0 <= j1 < y@.len() && 0 <= j2 < y@.len() &&
            0 <= k1 < z@.len() && 0 <= k2 < z@.len() ==>
            ((i1 != i2 || j1 != j2 || k1 != k2) ==> 
             (result@[i1][j1][k1] != result@[i2][j2][k2] || 
              (x@[i1] == x@[i2] && y@[j1] == y@[j2] && z@[k1] == z@[k2])))
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();
    let mut i = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x@.len(),
            result@.len() == i,
            forall|ii: int| 0 <= ii < i ==> result@[ii].len() == y@.len(),
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < result@[ii].len() ==> result@[ii][jj].len() == z@.len(),
    {
        let mut row: Vec<Vec<f64>> = Vec::new();
        let mut j = 0;
        
        while j < y.len()
            invariant
                0 <= j <= y@.len(),
                row@.len() == j,
                forall|jj: int| 0 <= jj < j ==> row@[jj].len() == z@.len(),
        {
            let mut col: Vec<f64> = Vec::new();
            let mut k = 0;
            
            while k < z.len()
                invariant
                    0 <= k <= z@.len(),
                    col@.len() == k,
            {
                let unique_val = get_unique_value(x[i], y[j], z[k], 1.0);
                col.push(unique_val);
                k += 1;
            }
            
            row.push(col);
            j += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}