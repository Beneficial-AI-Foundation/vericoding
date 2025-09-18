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
/* code modified by LLM (iteration 5): Fixed `index out of bounds` errors for `x` and `y` vectors by properly asserting the bounds, as well as fixing other minor verification errors. */
{
    let mut grid_x: Vec<Vec<f32>> = Vec::new();
    let mut grid_y: Vec<Vec<f32>> = Vec::new();

    let x_len = x.len();
    let y_len = y.len();

    assert(x_len > 0);
    assert(y_len > 0);

    for i in 0..y_len
        invariant 
            0 <= i <= y_len,
            grid_x.len() == i,
            grid_y.len() == i,
            forall|k: int| 0 <= k < i ==> grid_x[k].len() == x_len,
            forall|k: int| 0 <= k < i ==> grid_y[k].len() == x_len,
            forall|r: int, c: int| 0 <= r < i && 0 <= c < x_len ==> grid_x[r].view()[c] == x.view()[c],
            forall|r: int, c: int| 0 <= r < i && 0 <= c < x_len ==> grid_y[r].view()[c] == y.view()[r],
            y.len() == y_len,
            x.len() == x_len,
    {
        let mut row_x: Vec<f32> = Vec::new();
        let mut row_y: Vec<f32> = Vec::new();

        for j in 0..x_len
            invariant 
                0 <= j <= x_len,
                row_x.len() == j,
                row_y.len() == j,
                x.len() == x_len,
                y.len() == y_len,
                0 <= i < y_len,
                forall|k: int| 0 <= k < j ==> row_x.view()[k] == x.view()[k],
                forall|k: int| 0 <= k < j ==> row_y.view()[k] == y.view()[i as int],
        {
            row_x.push(x[j as usize]);
            row_y.push(y[i as usize]);
        }

        grid_x.push(row_x);
        grid_y.push(row_y);
    }

    (grid_x, grid_y)
}
// </vc-code>

}
fn main() {}