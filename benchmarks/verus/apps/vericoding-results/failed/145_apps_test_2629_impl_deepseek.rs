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
/* helper modified by LLM (iteration 5): Fix type conversion from nat to i8 with proper proof */
proof fn spiral_order_correct(n: nat, row: nat, col: nat) -> (value: i8)
    requires
        n >= 1,
        row < n,
        col < n
    ensures
        value as int == spiral_order(row as int, col as int, n as int) + 1
{
    let row_int = row as int;
    let col_int = col as int;
    let n_int = n as int;
    
    proof {
        assert(0 <= row_int < n_int);
        assert(0 <= col_int < n_int);
        assert(n_int >= 1);
    }
    
    let layer = min(min(row_int, col_int), min(n_int-1-row_int, n_int-1-col_int));
    let layer_start = 4 * layer * (n_int - layer - 1) + layer;
    
    let computed_value = if row_int == layer {
        layer_start + (col_int - layer) + 1
    } else if col_int == n_int - 1 - layer {
        layer_start + (n_int - 2 * layer - 1) + (row_int - layer) + 1
    } else if row_int == n_int - 1 - layer {
        layer_start + 2 * (n_int - 2 * layer - 1) + (n_int - 1 - layer - col_int) + 1
    } else {
        layer_start + 3 * (n_int - 2 * layer - 1) + (n_int - 1 - layer - row_int) + 1
    };
    
    proof {
        assert(computed_value == spiral_order(row_int, col_int, n_int) + 1);
    }
    
    computed_value as i8
}
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
    /* code modified by LLM (iteration 5): Use explicit ghost blocks and avoid nat conversion in exec code */
    let n_size = n as usize;
    let mut matrix = Vec::with_capacity(n_size);
    let mut i: usize = 0;
    while i < n_size
        invariant
            i <= n_size,
            matrix@.len() == i,
            forall |k: int| 0 <= k < i ==> matrix@[k].len() == n as int,
            forall |r: int, c: int| 0 <= r < i && 0 <= c < n as int ==> 1 <= matrix@[r][c] as int <= (n as int) * (n as int),
            forall |r: int, c: int| 0 <= r < i && 0 <= c < n as int ==> matrix@[r][c] as int == spiral_order(r, c, n as int) + 1
    {
        let mut row_vec = Vec::with_capacity(n_size);
        let mut j: usize = 0;
        while j < n_size
            invariant
                j <= n_size,
                row_vec@.len() == j,
                forall |c: int| 0 <= c < j ==> 1 <= row_vec@[c] as int <= (n as int) * (n as int),
                forall |c: int| 0 <= c < j ==> row_vec@[c] as int == spiral_order(i as int, c, n as int) + 1
        {
            proof {
                assert((n as int) >= 1);
                assert((i as int) < n as int);
                assert((j as int) < n as int);
            }
            let value: i8;
            proof {
                value = spiral_order_correct(n as nat, i as nat, j as nat);
            }
            row_vec.push(value);
            j += 1;
        }
        matrix.push(row_vec);
        i += 1;
    }
    matrix
}
// </vc-code>


}

fn main() {}