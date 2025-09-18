// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
use std::mem;

fn min_usize_exec(a: usize, b: usize) -> (r: usize)
    ensures r == if a <= b {a} else {b}
{
    if a <= b {a} else {b}
}

/* helper modified by LLM (iteration 4): Used std::mem::swap to swap entire rows and avoid unsupported &mut indexing */
fn swap_rows(mat: &mut Vec<Vec<f32>>, i: usize, j: usize)
    requires 0 <= i < mat.len(), 0 <= j < mat.len(),
        forall|k: int| 0 <= k < mat.len() ==> #[trigger] mat@[k].len() == mat@[0].len(),
    ensures mat@[i as int] == old(mat)[j as int], mat@[j as int] == old(mat)[i as int],
        forall|k: int| k != i as int && k != j as int && 0 <= k < mat.len() ==> mat@[k] == old(mat)[k]
{
    std::mem::swap(&mut mat[i], &mut mat[j]);
}
// </vc-helpers>

// <vc-spec>
spec fn min_usize(a: usize, b: usize) -> usize {
    if a <= b { a } else { b }
}

fn matrix_rank(A: Vec<Vec<f32>>) -> (result: usize)
    requires 
        A.len() > 0,
        A[0].len() > 0,
        forall|i: int| 0 <= i < A.len() ==> #[trigger] A[i].len() == A[0].len(),
    ensures
        result <= min_usize(A.len(), A[0].len()),

        (forall|i: int, j: int| 0 <= i < A.len() && 0 <= j < A[0].len() ==> #[trigger] A[i][j] == 0.0f32) ==> result == 0,

        (A.len() == A[0].len() && forall|i: int, j: int| 0 <= i < A.len() && 0 <= j < A[0].len() ==> #[trigger] A[i][j] == (if i == j { 1.0f32 } else { 0.0f32 })) ==> result == A.len(),

        (A.len() == 1 && A[0].len() == 1) ==> ((result == 1) <==> (A[0][0] != 0.0f32)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Replaced @ indexing with [] for correct exec Vec access to fix compilation */
    let mut a = A;
    let mut pivot = 0;
    let rows = a.len();
    let cols = a[0].len();
    let min_dim = min_usize_exec(rows, cols);
    for col in 0..min_dim {
        let mut pivot_row = pivot;
        while pivot_row < rows && a[pivot_row][col] == 0.0f32 {
            pivot_row += 1;
        }
        if pivot_row < rows {
            if pivot_row != pivot {
                swap_rows(&mut a, pivot, pivot_row);
            }
            for r in (pivot + 1)..rows {
                if a[r][col] != 0.0f32 {
                    let factor = a[r][col] / a[pivot][col];
                    for c in 0..cols {
                        a[r][c] -= factor * a[pivot][c];
                    }
                }
            }
            pivot += 1;
        }
    }
    pivot
}
// </vc-code>

}
fn main() {}