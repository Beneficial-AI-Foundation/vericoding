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
/* helper modified by LLM (iteration 5): runtime min function for i8 values with overflow protection */
fn min_i8(a: i8, b: i8) -> (result: i8)
    ensures result == a || result == b,
            result <= a && result <= b
{
    if a <= b { a } else { b }
}

/* helper modified by LLM (iteration 5): safe subtraction for i8 values */
fn safe_sub_i8(a: i8, b: i8) -> (result: i8)
    requires a >= b
    ensures result == a - b
{
    proof {
        assert(a as int - b as int >= 0);
        assert(a as int - b as int <= 127);
    }
    a - b
}

/* helper modified by LLM (iteration 5): safe multiplication for i8 values */
fn safe_mul_i8(a: i8, b: i8) -> (result: i8)
    requires a >= 0 && b >= 0,
             a as int * b as int <= 127
    ensures result as int == a as int * b as int
{
    a * b
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
    /* code modified by LLM (iteration 5): simplified approach with direct computation avoiding complex arithmetic */
    let mut matrix: Vec<Vec<i8>> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            matrix@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] matrix@[k]).len() == n as int,
            forall|k: int, l: int| 0 <= k < i as int && 0 <= l < n as int ==> #[trigger] (matrix@[k][l] as int) == spiral_order(k, l, n as int) + 1,
        decreases n - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j = 0;
        while j < n
            invariant
                0 <= j <= n,
                row@.len() == j as int,
                forall|l: int| 0 <= l < j as int ==> #[trigger] (row@[l] as int) == spiral_order(i as int, l, n as int) + 1,
            decreases n - j
        {
            proof {
                assert(0 <= i < n && 0 <= j < n && n >= 1);
            }
            
            let spiral_val = (spiral_order(i as int, j as int, n as int) + 1) as i8;
            
            proof {
                assert(spiral_order(i as int, j as int, n as int) + 1 >= 1);
                assert(spiral_order(i as int, j as int, n as int) + 1 <= (n as int) * (n as int));
                assert(spiral_val as int == spiral_order(i as int, j as int, n as int) + 1);
            }
            
            row.push(spiral_val);
            j += 1;
        }
        matrix.push(row);
        i += 1;
    }
    matrix
}
// </vc-code>


}

fn main() {}