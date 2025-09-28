// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn spiral_order(row: int, col: int, n: int) -> int
    recommends 0 <= row < n && 0 <= col < n && n >= 1
    decreases n - 2 * min(min(row, col), min(n-1-row, n-1-col)) - 1
{
    let layer = min(min(row, col), min(n-1-row, n-1-col));
    let layer_start = 4 * layer * (n - layer - 1) + layer;

    if row == layer {
        /* Top row of current layer */
        layer_start + (col - layer)
    } else if col == n - 1 - layer {
        /* Right column of current layer */
        layer_start + (n - 2 * layer - 1) + (row - layer)
    } else if row == n - 1 - layer {
        /* Bottom row of current layer */
        layer_start + 2 * (n - 2 * layer - 1) + (n - 1 - layer - col)
    } else {
        /* Left column of current layer */
        layer_start + 3 * (n - 2 * layer - 1) + (n - 1 - layer - row)
    }
}

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn valid_spiral_matrix(matrix: &Vec<Vec<int>>, n: int) -> bool {
    matrix.len() == n &&
    (forall|i: int| 0 <= i < n ==> (#[trigger] matrix[i]).len() == n) &&
    (forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger] matrix[i][j] == spiral_order(i, j, n) + 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn generate_matrix(n: i8) -> (matrix: Vec<Vec<i8>>)
    requires 
        valid_input(n as int)
    ensures 
        matrix@.len() == n as int && (forall|i: int| 0 <= i < n as int ==> (#[trigger] matrix@[i]).len() == n as int) &&
        (forall|i: int, j: int| 0 <= i < n as int && 0 <= j < n as int ==> 1 <= #[trigger] (matrix@[i][j] as int) <= (n as int) * (n as int)) &&
        (forall|i: int, j: int| 0 <= i < n as int && 0 <= j < n as int ==> #[trigger] (matrix@[i][j] as int) == spiral_order(i, j, n as int) + 1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implement spiral matrix generation by computing the order directly in exec code using integer arithmetic */
{
    let mut matrix: Vec<Vec<i8>> = Vec::new();
    for i in 0..(n as usize) {
        let mut row: Vec<i8> = Vec::new();
        for j in 0..(n as usize) {
            let row_int = i as i32;
            let col_int = j as i32;
            let nn_int = n as i32;
            let layer = if row_int <= col_int { if row_int <= nn_int - 1 - row_int { if row_int <= nn_int - 1 - col_int { row_int } else { nn_int - 1 - col_int } } else { if nn_int - 1 - row_int <= nn_int - 1 - col_int { nn_int - 1 - row_int } else { nn_int - 1 - col_int } } } else { if col_int <= nn_int - 1 - row_int { if col_int <= nn_int - 1 - col_int { col_int } else { nn_int - 1 - col_int } } else { if nn_int - 1 - row_int <= nn_int - 1 - col_int { nn_int - 1 - row_int } else { nn_int - 1 - col_int } } };
            let layer_start = 4 * layer * (nn_int - layer - 1) + layer;
            let spiral_pos =
                if row_int == layer {
                    layer_start + (col_int - layer)
                } else if col_int == nn_int - 1 - layer {
                    layer_start + (nn_int - 2 * layer - 1) + (row_int - layer)
                } else if row_int == nn_int - 1 - layer {
                    layer_start + 2 * (nn_int - 2 * layer - 1) + (nn_int - 1 - layer - col_int)
                } else {
                    layer_start + 3 * (nn_int - 2 * layer - 1) + (nn_int - 1 - layer - row_int)
                };
            let val = (spiral_pos + 1) as i8;
            row.push(val);
        }
        matrix.push(row);
    }
    matrix
}
// </vc-code>


}

fn main() {}