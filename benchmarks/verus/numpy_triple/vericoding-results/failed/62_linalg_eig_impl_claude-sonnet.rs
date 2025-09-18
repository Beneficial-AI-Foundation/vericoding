// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_square_matrix(a: &Vec<Vec<f32>>) -> bool {
    a.len() > 0 && forall|i: int| 0 <= i < a.len() ==> a[i].len() == a.len()
}

spec fn is_diagonal_matrix(a: &Vec<Vec<f32>>) -> bool {
    forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && i != j ==> a[i][j] == 0.0f32
}

fn extract_diagonal(a: &Vec<Vec<f32>>) -> (eigenvalues: Vec<f32>)
    requires
        is_square_matrix(a),
    ensures
        eigenvalues.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> eigenvalues[i] == a[i][i],
{
    let mut eigenvalues = Vec::new();
    let mut idx = 0;
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            eigenvalues.len() == idx,
            forall|i: int| 0 <= i < idx ==> eigenvalues[i] == a[i][i],
            forall|i: int| 0 <= i < a.len() ==> a[i].len() == a.len(),
        decreases a.len() - idx
    {
        eigenvalues.push(a[idx][idx]);
        idx += 1;
    }
    eigenvalues
}

/* helper modified by LLM (iteration 5): fixed type casting issues */
fn create_identity_matrix(n: usize) -> (eigenvectors: Vec<Vec<f32>>)
    requires n > 0,
    ensures
        eigenvectors.len() == n,
        forall|i: int| 0 <= i < eigenvectors.len() ==> eigenvectors[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> 
            (i == j ==> eigenvectors[i][j] == 1.0f32) &&
            (i != j ==> eigenvectors[i][j] == 0.0f32),
        forall|col: int| 0 <= col < n ==> eigenvectors[col][col] == 1.0f32,
        forall|col: int| 0 <= col < n ==> exists|row: int| 0 <= row < n && eigenvectors[row][col] != 0.0f32,
{
    let mut eigenvectors: Vec<Vec<f32>> = Vec::new();
    let mut row = 0;
    while row < n
        invariant
            0 <= row <= n,
            eigenvectors.len() == row,
            forall|i: int| 0 <= i < row ==> eigenvectors[i].len() == n,
            forall|i: int, j: int| 0 <= i < row && 0 <= j < n ==> 
                (i == j ==> eigenvectors[i][j] == 1.0f32) &&
                (i != j ==> eigenvectors[i][j] == 0.0f32),
        decreases n - row
    {
        let mut current_row: Vec<f32> = Vec::new();
        let mut col = 0;
        while col < n
            invariant
                0 <= col <= n,
                current_row.len() == col,
                forall|j: int| 0 <= j < col ==> 
                    (row == j ==> current_row[j] == 1.0f32) &&
                    (row != j ==> current_row[j] == 0.0f32),
            decreases n - col
        {
            if row == col {
                current_row.push(1.0f32);
            } else {
                current_row.push(0.0f32);
            }
            col += 1;
        }
        eigenvectors.push(current_row);
        row += 1;
    }
    eigenvectors
}
// </vc-helpers>

// <vc-spec>
fn eig(a: Vec<Vec<f32>>) -> (result: (Vec<f32>, Vec<Vec<f32>>))
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i].len() == a.len(),
    ensures
        result.0.len() == a.len() && result.1.len() == a.len(),
        forall|i: int| 0 <= i < result.1.len() ==> result.1[i].len() == a.len(),

        true,

        (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && i != j ==> a[i][j] == 0.0f32) ==> 
        (forall|i: int| #![trigger a[i]] 0 <= i < a.len() ==> 
            exists|j: int| 0 <= j < result.0.len() && result.0[j] == a[i][i]),

        forall|col: int| #![trigger result.1[col]] 0 <= col < a.len() ==> 
            exists|row: int| 0 <= row < a.len() && result.1[row][col] != 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed type casting that caused compilation errors */
    let eigenvalues = extract_diagonal(&a);
    let eigenvectors = create_identity_matrix(a.len());
    
    proof {
        // Establish that eigenvalues contain diagonal elements when matrix is diagonal
        if is_diagonal_matrix(&a) {
            assert(forall|i: int| 0 <= i < a.len() ==> 
                exists|j: int| 0 <= j < eigenvalues.len() && eigenvalues[j] == a[i][i]) by {
                assert(forall|i: int| 0 <= i < a.len() ==> eigenvalues[i] == a[i][i]);
            };
        }
        
        // Establish eigenvector property - identity matrix has non-zero diagonal elements
        assert(forall|col: int| 0 <= col < a.len() ==> 
            exists|row: int| 0 <= row < a.len() && eigenvectors[row][col] != 0.0f32) by {
            assert(forall|col: int| 0 <= col < a.len() ==> eigenvectors[col][col] == 1.0f32);
        };
    }
    
    (eigenvalues, eigenvectors)
}
// </vc-code>

}
fn main() {}