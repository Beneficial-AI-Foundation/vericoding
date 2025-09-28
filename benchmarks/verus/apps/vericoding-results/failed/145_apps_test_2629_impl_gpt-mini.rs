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
/* helper modified by LLM (iteration 4): dummy helper for proofs */
proof fn helpers_dummy() {
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
    /* code modified by LLM (iteration 4): generate spiral matrix using i32 runtime arithmetic and proofs */
    let mut matrix: Vec<Vec<i8>> = Vec::new();
    let mut i: i8 = 0;
    while i < n
        invariant
            0 <= i as int && i as int <= n as int,
            matrix@.len() == i as int,
            (forall|ri: int, cj: int| 0 <= ri < i as int && 0 <= cj < n as int ==> #[trigger] (matrix@[ri][cj] as int) == spiral_order(ri, cj, n as int) + 1),
        decreases n as int - i as int
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: i8 = 0;
        while j < n
            invariant
                0 <= j as int && j as int <= n as int,
                row@.len() == j as int,
                (forall|ci: int| 0 <= ci < j as int ==> #[trigger] (row@[ci] as int) == spiral_order(i as int, ci, n as int) + 1),
            decreases n as int - j as int
        {
            let ii = i as i32;
            let jj = j as i32;
            let nn = n as i32;
            let mut layer = ii;
            if jj < layer { layer = jj; }
            if nn - 1 - ii < layer { layer = nn - 1 - ii; }
            if nn - 1 - jj < layer { layer = nn - 1 - jj; }
            let layer_start = 4 * layer * (nn - layer - 1) + layer;
            let val = if ii == layer {
                layer_start + (jj - layer)
            } else if jj == nn - 1 - layer {
                layer_start + (nn - 2 * layer - 1) + (ii - layer)
            } else if ii == nn - 1 - layer {
                layer_start + 2 * (nn - 2 * layer - 1) + (nn - 1 - layer - jj)
            } else {
                layer_start + 3 * (nn - 2 * layer - 1) + (nn - 1 - layer - ii)
            };
            let v = #[verifier::truncate] ((val + 1) as i8);
            row.push(v);
            proof {
                // Relate the just-pushed runtime value to the spec spiral_order
                assert((row@[j as int] as int) == (val as int) + 1);
                let spec_val = spiral_order(i as int, j as int, n as int);
                // Recompute the expected value in ghost (int) arithmetic
                let ii_int = i as int;
                let jj_int = j as int;
                let nn_int = n as int;
                let mut layer_int = ii_int;
                if jj_int < layer_int { layer_int = jj_int; }
                if nn_int - 1 - ii_int < layer_int { layer_int = nn_int - 1 - ii_int; }
                if nn_int - 1 - jj_int < layer_int { layer_int = nn_int - 1 - jj_int; }
                let layer_start_int = 4 * layer_int * (nn_int - layer_int - 1) + layer_int;
                let calc = if ii_int == layer_int {
                    layer_start_int + (jj_int - layer_int)
                } else if jj_int == nn_int - 1 - layer_int {
                    layer_start_int + (nn_int - 2 * layer_int - 1) + (ii_int - layer_int)
                } else if ii_int == nn_int - 1 - layer_int {
                    layer_start_int + 2 * (nn_int - 2 * layer_int - 1) + (nn_int - 1 - layer_int - jj_int)
                } else {
                    layer_start_int + 3 * (nn_int - 2 * layer_int - 1) + (nn_int - 1 - layer_int - ii_int)
                };
                // Connect the runtime computed val (i32) with the ghost computation (int)
                assert(val as int == calc);
                assert(spec_val == calc);
                assert((row@[j as int] as int) == spec_val + 1);
            }
            j = j + 1;
        }
        matrix.push(row);
        proof {
            assert(matrix@[i as int].len() == n as int);
            assert(forall|cj: int| 0 <= cj < n as int ==> (matrix@[i as int][cj] as int) == spiral_order(i as int, cj, n as int) + 1);
        }
        i = i + 1;
    }
    matrix
}

// </vc-code>


}

fn main() {}