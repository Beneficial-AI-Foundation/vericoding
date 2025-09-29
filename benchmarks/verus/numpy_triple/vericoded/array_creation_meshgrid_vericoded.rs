// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn meshgrid(x: Vec<f32>, y: Vec<f32>) -> (result: (Vec<Vec<f32>>, Vec<Vec<f32>>))
    requires 
        x.len() > 0,
        y.len() > 0,
    ensures
        result.0.len() == y.len(),
        result.1.len() == y.len(),
        forall|i: int| 0 <= i < y.len() ==> result.0[i].len() == x.len(),
        forall|i: int| 0 <= i < y.len() ==> result.1[i].len() == x.len(),
        forall|i: int, j: int| 0 <= i < y.len() && 0 <= j < x.len() ==> result.0[i][j] == x[j],
        forall|i: int, j: int| 0 <= i < y.len() && 0 <= j < x.len() ==> result.1[i][j] == y[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch by casting i to int for y access */
    let mut xx: Vec<Vec<f32>> = Vec::new();
    let mut yy: Vec<Vec<f32>> = Vec::new();
    
    let mut i = 0;
    while i < y.len()
        invariant
            i <= y.len(),
            xx.len() == i,
            yy.len() == i,
            forall|k: int| 0 <= k < i ==> xx[k].len() == x.len(),
            forall|k: int| 0 <= k < i ==> yy[k].len() == x.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < x.len() ==> xx[k][j] == x[j],
            forall|k: int, j: int| 0 <= k < i && 0 <= j < x.len() ==> yy[k][j] == y[k],
        decreases y.len() - i
    {
        let mut x_row: Vec<f32> = Vec::new();
        let mut y_row: Vec<f32> = Vec::new();
        
        let mut j = 0;
        while j < x.len()
            invariant
                j <= x.len(),
                x_row.len() == j,
                y_row.len() == j,
                i < y.len(),
                forall|k: int| 0 <= k < j ==> x_row[k] == x[k],
                forall|k: int| 0 <= k < j ==> y_row[k] == y[i as int],
            decreases x.len() - j
        {
            x_row.push(x[j]);
            y_row.push(y[i]);
            j += 1;
        }
        
        xx.push(x_row);
        yy.push(y_row);
        i += 1;
    }
    
    (xx, yy)
}
// </vc-code>

}
fn main() {}