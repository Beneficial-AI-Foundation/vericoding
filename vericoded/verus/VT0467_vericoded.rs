// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn laggrid3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, c: Vec<Vec<Vec<f64>>>) -> (result: Vec<Vec<Vec<f64>>>)
    requires 
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c@[i].len() ==> c@[i]@[j].len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result@[i].len() == y.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result@[i].len() ==> result@[i]@[j].len() == z.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clauses to all while loops */
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();
    
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|k: int| 0 <= k < result.len() ==> result@[k].len() == y.len(),
            forall|k: int, l: int| 0 <= k < result.len() && 0 <= l < result@[k].len() ==> result@[k]@[l].len() == z.len(),
        decreases x.len() - i
    {
        let mut row: Vec<Vec<f64>> = Vec::new();
        
        let mut j: usize = 0;
        while j < y.len()
            invariant
                j <= y.len(),
                row.len() == j,
                forall|l: int| 0 <= l < row.len() ==> row@[l].len() == z.len(),
            decreases y.len() - j
        {
            let mut col: Vec<f64> = Vec::new();
            
            let mut k: usize = 0;
            while k < z.len()
                invariant
                    k <= z.len(),
                    col.len() == k,
                decreases z.len() - k
            {
                col.push(0.0);
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