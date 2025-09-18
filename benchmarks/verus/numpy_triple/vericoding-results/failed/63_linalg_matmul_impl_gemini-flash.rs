// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `to_seq()` and `sum()` usage, fixed `usize` to `int` casting for indexing, and used `as int` for comparisons. Used `spec_index` for `Seq` access.*/
fn dot_product(row: Seq<f32>, col: Seq<f32>) -> f32
    requires
        row.len() == col.len()
    ensures
        true // For simplicity, we just need to compute the sum
{
    let mut sum: f32 = 0.0;
    let mut k: nat = 0; // Changed to nat
    while (k as int) < row.len()
        invariant
            0 <= k,
            (k as int) <= row.len(),
            sum == (0..k).to_seq().map(|j: nat| row.spec_index(j as int) * col.spec_index(j as int)).sum::<f32>()
    {
        sum = sum + row.spec_index(k as int) * col.spec_index(k as int);
        k = k + 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn matmul(A: Vec<Vec<f32>>, B: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires
        A.len() > 0,
        B.len() > 0,
        A@[0].len() == B.len(),
        forall|i: int| 0 <= i < A.len() ==> #[trigger] A@[i].len() == A@[0].len(),
        forall|i: int| 0 <= i < B.len() ==> #[trigger] B@[i].len() == B@[0].len(),
    ensures
        result.len() == A.len(),
        result.len() > 0 ==> result@[0].len() == B@[0].len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result@[i].len() == B@[0].len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed `index()` to `spec_index()` for Seq, converted `usize` to `nat/int` where necessary, fixed a bunch of method resolution issues and to_seq/to_vec errors. */
{
    let n_rows_A = A.len();
    let n_cols_A = A.spec_index(0).len();
    let n_rows_B = B.len();
    let n_cols_B = B.spec_index(0).len();

    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: nat = 0;

    while (i as int) < n_rows_A
        invariant
            0 <= i,
            (i as int) <= n_rows_A,
            result.len() == (i as int),
            forall|idx: int| 0 <= idx < (i as int) ==> 
                result.spec_index(idx).len() == n_cols_B,
            forall|idx_i: int, idx_j: int| 0 <= idx_i < (i as int) && 0 <= idx_j < (n_cols_B as int) ==> 
                result.spec_index(idx_i).spec_index(idx_j) == {
                    let mut col_vec: Vec<f32> = Vec::new();
                    let mut k_idx: nat = 0;
                    while (k_idx as int) < n_rows_B {
                        col_vec.push(B.spec_index(k_idx as int).spec_index(idx_j as int));
                        k_idx = k_idx + 1;
                    }
                    dot_product(A.spec_index(idx_i), col_vec.to_seq())
                }
    {
        let mut current_row: Vec<f32> = Vec::new();
        let mut j: nat = 0;

        while (j as int) < n_cols_B
            invariant
                0 <= j,
                (j as int) <= n_cols_B,
                current_row.len() == (j as int),
                forall|idx: int| 0 <= idx < (j as int) ==> 
                    current_row.spec_index(idx) == {
                        let mut col_vec: Vec<f32> = Vec::new();
                        let mut k_idx: nat = 0;
                        while (k_idx as int) < n_rows_B {
                            col_vec.push(B.spec_index(k_idx as int).spec_index(idx as int));
                            k_idx = k_idx + 1;
                        }
                        dot_product(A.spec_index(i as int), col_vec.to_seq())
                    }
        {
            let mut col_j_vec: Vec<f32> = Vec::new();
            let mut k: nat = 0;
            while (k as int) < n_rows_B
                invariant
                    0 <= k,
                    (k as int) <= n_rows_B,
                    col_j_vec.len() == (k as int)
            {
                col_j_vec.push(B.spec_index(k as int).spec_index(j as int));
                k = k + 1;
            }
            current_row.push(dot_product(A.spec_index(i as int), col_j_vec.to_seq()));
            j = j + 1;
        }
        result.push(current_row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}