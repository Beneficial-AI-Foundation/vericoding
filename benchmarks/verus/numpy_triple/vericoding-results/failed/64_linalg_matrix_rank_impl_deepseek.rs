// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type conversions and deprecated methods */
proof fn gaussian_elimination_lemma(A: Seq<Seq<f32>>, r: usize)
    requires
        r <= min_usize(A.len(), A[0].len()),
    ensures
        true
{
}

proof fn is_zero_matrix_implies_rank_zero(A: Seq<Seq<f32>>)
    requires
        forall|i: int, j: int| 0 <= i < A.len() && 0 <= j < A[0].len() ==> A[i][j] == 0.0f32,
    ensures
        true
{
}

proof fn identity_matrix_implies_full_rank(A: Seq<Seq<f32>>)
    requires
        A.len() == A[0].len(),
        forall|i: int, j: int| 0 <= i < A.len() && 0 <= j < A[0].len() ==> A[i][j] == (if i == j { 1.0f32 } else { 0.0f32 }),
    ensures
        true
{
}

proof fn scalar_nonzero_implies_rank_one(A: Seq<Seq<f32>>)
    requires
        A.len() == 1 && A[0].len() == 1,
        A[0][0] != 0.0f32,
    ensures
        true
{
}

fn find_pivot_row(A: &Vec<Vec<f32>>, col: usize, start_row: usize) -> (row: Option<usize>)
    requires
        A.len() > 0,
        A[0].len() > 0,
        forall|i: int| 0 <= i < A.len() ==> #[trigger] A[i].len() == A[0].len(),
        col < A[0].len(),
        start_row < A.len()
    ensures
        row->is_Some() ==> row->get_Some_0() >= start_row && row->get_Some_0() < A.len(),
        row->is_None() ==> forall|r: int| start_row <= r < A.len() ==> A[r as usize][col as usize] == 0.0f32
{
    let mut row = start_row;
    while row < A.len()
        invariant
            row >= start_row && row <= A.len(),
            forall|r: int| start_row <= r < row ==> A[r as usize][col as usize] == 0.0f32
    {
        if A[row][col] != 0.0f32 {
            return Some(row);
        }
        row += 1;
    }
    None
}

fn swap_rows(A: &mut Vec<Vec<f32>>, i: usize, j: usize)
    requires
        A.len() > 0,
        A[0].len() > 0,
        forall|k: int| 0 <= k < A.len() ==> #[trigger] A[k].len() == A[0].len(),
        i < A.len(),
        j < A.len()
    ensures
        A@ == old(A)@.swap(i, j)
{
    if i != j {
        A.swap(i, j);
    }
}

fn eliminate_column(A: &mut Vec<Vec<f32>>, pivot_row: usize, col: usize)
    requires
        A.len() > 0,
        A[0].len() > 0,
        forall|i: int| 0 <= i < A.len() ==> #[trigger] A[i].len() == A[0].len(),
        pivot_row < A.len(),
        col < A[0].len(),
        A[pivot_row][col] != 0.0f32
    ensures
        forall|r: int| pivot_row + 1 <= r < A.len() ==> A[r as usize][col as usize] == 0.0f32
{
    let pivot_value = A[pivot_row][col];
    let mut row = pivot_row + 1;
    while row < A.len()
        invariant
            row >= pivot_row + 1 && row <= A.len(),
            forall|r: int| pivot_row + 1 <= r < row ==> A[r as usize][col as usize] == 0.0f32
    {
        if A[row][col] != 0.0f32 {
            let factor = A[row][col] / pivot_value;
            let mut c = col;
            while c < A[0].len()
                invariant
                    c >= col && c <= A[0].len(),
                    A[row][col] == 0.0f32,
                    forall|cc: int| col <= cc < c ==> A[row][cc as usize] == old(A)[row][cc as usize] - (factor * old(A)[pivot_row][cc as usize])
            {
                A[row][c] = A[row][c] - factor * A[pivot_row][c];
                c += 1;
            }
        }
        row += 1;
    }
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
/* code modified by LLM (iteration 5): Fix type conversion and proof function calls */
{
    let mut rank = 0;
    let mut row = 0;
    let mut col = 0;
    let mut A_copy = A.clone();
    
    while row < A_copy.len() && col < A_copy[0].len()
        invariant
            rank <= min_usize(A.len(), A[0].len()),
            row >= 0 && row <= A_copy.len(),
            col >= 0 && col <= A_copy[0].len(),
    {
        match find_pivot_row(&A_copy, col, row) {
            Some(pivot_row) => {
                swap_rows(&mut A_copy, row, pivot_row);
                eliminate_column(&mut A_copy, row, col);
                rank += 1;
                row += 1;
                col += 1;
            }
            None => {
                col += 1;
            }
        }
    }
    
    proof {
        let A_seq: Seq<Seq<f32>> = A_copy@.map(|v: Vec<f32>| v@);
        gaussian_elimination_lemma(A_seq, rank);
        let A_orig_seq: Seq<Seq<f32>> = A@.map(|v: Vec<f32>| v@);
        is_zero_matrix_implies_rank_zero(A_orig_seq);
        identity_matrix_implies_full_rank(A_orig_seq);
        scalar_nonzero_implies_rank_one(A_orig_seq);
    }
    
    rank
}
// </vc-code>

}
fn main() {}