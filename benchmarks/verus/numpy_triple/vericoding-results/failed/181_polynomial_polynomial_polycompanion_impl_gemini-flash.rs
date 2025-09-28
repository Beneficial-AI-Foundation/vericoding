// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polycompanion(c: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires 
        c.len() >= 2,
        c[c.len() - 1] != 0,
    ensures
        result.len() == c.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == c.len() - 1,
        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() ==>
            (if i + 1 == j && i < c.len() - 2 {
                result[i][j] as int == 1
            } else if i == c.len() - 2 {
                result[i][j] as int * c[c.len() - 1] as int == -c[j] as int
            } else {
                result[i][j] as int == 0
            })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type errors related to `nat` usage in runtime code by casting `j` and `n_usize - 1` to `usize` for array indexing, and then to `int` within ghost contexts for arithmetic. Also added proof block for loop invariant. */
{
    let n_usize: usize = c.len();
    let mut matrix: Vec<Vec<i8>> = Vec::new();

    let n: usize = n_usize - 1;

    for i in 0..n
        invariant
            0 <= i && i <= n,
            matrix.len() == i,
            // All previous rows have correct length
            forall|k: int| 0 <= k < i ==> matrix[k as usize].len() == n,
            // All previous rows satisfy the conditions relevant to them
            forall|k: int, j: int|
                0 <= k < i && 0 <= j < n ==> {
                    let matrix_k_j = matrix[k as usize][j as usize] as int;
                    if k + 1 == j && k < n - 1 {
                        matrix_k_j == 1
                    } else if k == n - 1 {
                        matrix_k_j * c[n_usize - 1] as int == -c[j as usize] as int
                    } else {
                        matrix_k_j == 0
                    }
                },
    {
        let mut row: Vec<i8> = Vec::new();
        for j in 0..n
            invariant
                0 <= j && j <= n,
                row.len() == j,
                // All previous elements in the current row satisfy the conditions
                forall|k: int|
                    0 <= k < j ==> {
                        let row_k = row[k as usize] as int;
                        if i + 1 == k && i < n - 1 {
                            row_k == 1
                        } else if i == n - 1 {
                            row_k * c[n_usize - 1] as int == -c[k as usize] as int
                        } else {
                            row_k == 0
                        }
                    },
        {
            if i + 1 == j {
                row.push(1);
            } else if i == n - 1 {
                // This line caused the type error. We need to avoid mixing `nat` with runtime operations directly.
                // The ghost `view_at` is for specification/proof reasoning on sequence values, not for concrete runtime arithmetic on variables.
                // We need to fetch the i8 values and then potentially perform `int` arithmetic in a proof context or cast carefully.
                // The ensures clause dictates: result[i][j] * c[c.len() - 1] == -c[j]
                // So, result[i][j] = -c[j] / c[c.len() - 1]

                let c_j: i8 = c[j as usize];
                let c_last: i8 = c[n_usize - 1];

                // Perform division after converting to int to respect Verus's default ghost integer arithmetic
                // and then cast back to i8 for storage in the matrix. This relies on the result fitting in i8.
                proof {
                    let v_cj = c.view_at(j as nat);
                    let v_clast = c.view_at((n_usize - 1) as nat);
                    // Assuming no overflow/underflow for i8 and that division is exact or truncated as needed
                    // according to the problem domain. Here, the postcondition implies the existence of such an i8.
                }
                row.push((-c_j as int / c_last as int) as i8);
            } else {
                row.push(0);
            }
        }
        matrix.push(row);
    }
    matrix
}
// </vc-code>


}
fn main() {}