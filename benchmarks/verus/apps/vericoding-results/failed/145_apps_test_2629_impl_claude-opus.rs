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
{
    /* code modified by LLM (iteration 5): Added decreases clauses to while loops */
    let mut matrix: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i <= n as int,
            matrix@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] matrix@[k]).len() == n as int,
            forall|r: int, c: int| 0 <= r < i as int && 0 <= c < n as int ==> #[trigger] (matrix@[r][c] as int) == spiral_order(r, c, n as int) + 1,
        decreases n as int - i as int
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < n as usize
            invariant
                0 <= j <= n as int,
                row@.len() == j as int,
                i < n as int,
                matrix@.len() == i as int,
                forall|k: int| 0 <= k < i as int ==> (#[trigger] matrix@[k]).len() == n as int,
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < n as int ==> #[trigger] (matrix@[r][c] as int) == spiral_order(r, c, n as int) + 1,
                forall|c: int| 0 <= c < j as int ==> #[trigger] (row@[c] as int) == spiral_order(i as int, c, n as int) + 1,
            decreases n as int - j as int
        {
            let ghost val_int: int = spiral_order(i as int, j as int, n as int) + 1;
            proof {
                assert(1 <= val_int <= (n as int) * (n as int));
                assert(val_int <= 127);
            }
            let val: i8 = 1 + (i * (n as usize) + j) as i8;
            proof {
                assert(val as int == spiral_order(i as int, j as int, n as int) + 1);
            }
            row.push(val);
            j = j + 1;
        }
        matrix.push(row);
        i = i + 1;
    }
    matrix
}
// </vc-code>


}

fn main() {}