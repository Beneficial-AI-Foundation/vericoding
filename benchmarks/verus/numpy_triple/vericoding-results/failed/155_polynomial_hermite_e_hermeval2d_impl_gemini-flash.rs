// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn hermite_basis(n: nat, t: int) -> int
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        t
    } else {
        t * hermite_basis((n - 1) as nat, t) - (n - 1) as int * hermite_basis((n - 2) as nat, t)
    }
}

spec fn matrix_sum(c: Seq<Vec<i8>>, x: int, y: int) -> int {
    let n = c.len() as int;
    if n == 0 {
        0
    } else {
        let m = c[0].len() as int;
        matrix_sum_helper(c, x, y, 0, n, m)
    }
}

spec fn matrix_sum_helper(c: Seq<Vec<i8>>, x: int, y: int, i: int, n: int, m: int) -> int
    decreases n - i
{
    if i >= n {
        0
    } else {
        row_sum_helper(c[i], x, y, i, 0, m) + matrix_sum_helper(c, x, y, i + 1, n, m)
    }
}

spec fn row_sum_helper(row: Vec<i8>, x: int, y: int, i: int, j: int, m: int) -> int
    decreases m - j
{
    if j >= m {
        0
    } else {
        (row[j] as int) * hermite_basis(i as nat, x) * hermite_basis(j as nat, y) + 
        row_sum_helper(row, x, y, i, j + 1, m)
    }
}

fn hermeval2d(x: Vec<i8>, y: Vec<i8>, c: Vec<Vec<i8>>) -> (result: Vec<i8>)
    requires
        x.len() == y.len(),
        x.len() > 0,
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> #[trigger] c[i].len() == c[0].len(),
        c[0].len() > 0,
    ensures
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> 
            result[k] as int == matrix_sum(c@, x[k] as int, y[k] as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Cast x_val and y_val primitive types directly as i8 and apply to hermite basis directly. Ghost variables moved to where they are used. */
    let mut result = Vec::new();
    let len = x.len();
    let c_len_x_u = c.len();
    let c_len_y_u = c[0].len();

    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            result.len() == k,
            forall|idx: int| 0 <= idx < k ==> result@[idx] as int == matrix_sum(c@, x@[idx] as int, y@[idx] as int),
    {
        let x_val_i8: i8 = x[k];
        let y_val_i8: i8 = y[k];

        let mut current_sum_val: i32 = 0;
        let mut i: usize = 0;
        while i < c_len_x_u
            invariant
                i <= c_len_x_u,
                result.len() == k,
                current_sum_val as int == matrix_sum_helper(c@, x_val_i8 as int, y_val_i8 as int, 0, i as int, c_len_y_u as int) ,

            decreases c_len_x_u - i
        {
            let mut row_sum_val: i32 = 0;
            let mut j: usize = 0;
            while j < c_len_y_u
                invariant
                    j <= c_len_y_u,
                    result.len() == k,
                    current_sum_val as int == matrix_sum_helper(c@, x_val_i8 as int, y_val_i8 as int, 0, i as int, c_len_y_u as int),
                    row_sum_val as int == row_sum_helper(c@[i], x_val_i8 as int, y_val_i8 as int, i as int, 0, j as int),
                decreases c_len_y_u - j
            {
                let ghost_i: nat = i as nat;
                let ghost_j: nat = j as nat;
                let term = (c@[i]@[j] as i32) *
                            (hermite_basis(ghost_i, x_val_i8 as int) as i32) *
                            (hermite_basis(ghost_j, y_val_i8 as int) as i32);

                row_sum_val = row_sum_val + term;

                j = j + 1;
            }
            proof {
                assert(row_sum_val as int == row_sum_helper(c@[i], x_val_i8 as int, y_val_i8 as int, i as int, 0, c_len_y_u as int));
            }
            current_sum_val = current_sum_val + row_sum_val;

            i = i + 1;
        }
        proof {
            assert(current_sum_val as int == matrix_sum_helper(c@, x_val_i8 as int, y_val_i8 as int, 0, c_len_x_u as int, c_len_y_u as int));
            assert(current_sum_val as int == matrix_sum(c@, x_val_i8 as int, y_val_i8 as int));
        }

        result.push(current_sum_val as i8);
        k = k + 1;
    }

    result
}
// </vc-code>


}
fn main() {}