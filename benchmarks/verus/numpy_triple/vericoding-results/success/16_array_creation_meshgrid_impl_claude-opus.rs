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
    /* code modified by LLM (iteration 3): Fixed indexing and loop invariant issues */
    let mut x_grid: Vec<Vec<f32>> = Vec::new();
    let mut y_grid: Vec<Vec<f32>> = Vec::new();
    
    let mut i: usize = 0;
    while i < y.len()
        invariant
            i <= y.len(),
            x_grid.len() == i,
            y_grid.len() == i,
            forall|k: int| 0 <= k < i ==> x_grid[k].len() == x.len(),
            forall|k: int| 0 <= k < i ==> y_grid[k].len() == x.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < x.len() ==> x_grid[k][j] == x[j],
            forall|k: int, j: int| 0 <= k < i && 0 <= j < x.len() ==> y_grid[k][j] == y[k],
        decreases y.len() - i
    {
        let mut x_row: Vec<f32> = Vec::new();
        let mut y_row: Vec<f32> = Vec::new();
        
        let mut j: usize = 0;
        while j < x.len()
            invariant
                i < y.len(),
                j <= x.len(),
                x_row.len() == j,
                y_row.len() == j,
                forall|k: int| 0 <= k < j ==> x_row[k] == x[k],
                forall|k: int| 0 <= k < j ==> y_row[k] == y[i as int],
            decreases x.len() - j
        {
            x_row.push(x[j]);
            y_row.push(y[i]);
            j = j + 1;
        }
        
        assert(x_row.len() == x.len());
        assert(y_row.len() == x.len());
        assert(forall|k: int| 0 <= k < x.len() ==> x_row[k] == x[k]);
        assert(forall|k: int| 0 <= k < x.len() ==> y_row[k] == y[i as int]);
        
        x_grid.push(x_row);
        y_grid.push(y_row);
        i = i + 1;
    }
    
    assert(x_grid.len() == y.len());
    assert(y_grid.len() == y.len());
    assert(forall|k: int| 0 <= k < y.len() ==> x_grid[k].len() == x.len());
    assert(forall|k: int| 0 <= k < y.len() ==> y_grid[k].len() == x.len());
    
    (x_grid, y_grid)
}
// </vc-code>

}
fn main() {}