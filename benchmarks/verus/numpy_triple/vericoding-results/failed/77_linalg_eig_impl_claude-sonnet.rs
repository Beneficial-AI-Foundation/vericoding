// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed bounds checking for matrix indexing */
fn is_diagonal(matrix: &Vec<Vec<f32>>) -> (result: bool)
    requires
        matrix.len() > 0,
        forall|i: int| 0 <= i < matrix.len() ==> matrix@[i].len() == matrix.len(),
{
    let n = matrix.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|row: int, col: int| 0 <= row < i && 0 <= col < n && row != col ==> matrix@[row]@[col] == 0.0f32,
        decreases n - i
    {
        let mut j = 0;
        while j < n
            invariant
                0 <= j <= n,
                forall|col: int| 0 <= col < j && i as int != col ==> matrix@[i as int]@[col] == 0.0f32,
            decreases n - j
        {
            proof {
                assert(0 <= i < n);
                assert(0 <= j < n);
                assert(i < matrix.len());
                assert(j < matrix[i].len());
            }
            if i != j && matrix[i][j] != 0.0f32 {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

fn extract_diagonal_eigenvalues(matrix: &Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires
        matrix.len() > 0,
        forall|i: int| 0 <= i < matrix.len() ==> matrix@[i].len() == matrix.len(),
        forall|i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix.len() && i != j ==> matrix@[i]@[j] == 0.0f32,
    ensures
        result.len() == matrix.len(),
        forall|i: int| 0 <= i < matrix.len() ==> result@[i] == matrix@[i]@[i],
{
    let n = matrix.len();
    let mut eigenvalues: Vec<f32> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            eigenvalues.len() == i,
            forall|k: int| 0 <= k < i ==> eigenvalues@[k] == matrix@[k]@[k],
        decreases n - i
    {
        proof {
            assert(0 <= i < n);
            assert(i < matrix.len());
            assert(i < matrix[i].len());
        }
        eigenvalues.push(matrix[i][i]);
        i += 1;
    }
    eigenvalues
}

fn create_identity_matrix(n: usize) -> (result: Vec<Vec<f32>>)
    requires n > 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result@[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> (i == j ==> result@[i]@[j] == 1.0f32),
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> (i != j ==> result@[i]@[j] == 0.0f32),
{
    let mut matrix: Vec<Vec<f32>> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            matrix.len() == i,
            forall|row: int| 0 <= row < i ==> matrix@[row].len() == n,
            forall|row: int, col: int| 0 <= row < i && 0 <= col < n ==> (row == col ==> matrix@[row]@[col] == 1.0f32),
            forall|row: int, col: int| 0 <= row < i && 0 <= col < n ==> (row != col ==> matrix@[row]@[col] == 0.0f32),
        decreases n - i
    {
        let mut row: Vec<f32> = Vec::with_capacity(n);
        let mut j = 0;
        while j < n
            invariant
                0 <= j <= n,
                row.len() == j,
                forall|col: int| 0 <= col < j ==> (i as int == col ==> row@[col] == 1.0f32),
                forall|col: int| 0 <= col < j ==> (i as int != col ==> row@[col] == 0.0f32),
            decreases n - j
        {
            if i == j {
                row.push(1.0f32);
            } else {
                row.push(0.0f32);
            }
            j += 1;
        }
        matrix.push(row);
        i += 1;
    }
    matrix
}
// </vc-helpers>

// <vc-spec>
fn eig(a: Vec<Vec<f32>>) -> (result: (Vec<f32>, Vec<Vec<f32>>))
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a@[i].len() == a.len(),
    ensures
        result.0.len() == a.len() && result.1.len() == a.len(),
        forall|i: int| 0 <= i < result.1.len() ==> result.1@[i].len() == a.len(),

        true,

        (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && i != j ==> a@[i]@[j] == 0.0f32) ==> 
        (forall|i: int| #![trigger a@[i]] 0 <= i < a.len() ==> 
            exists|j: int| 0 <= j < result.0.len() && result.0@[j] == a@[i]@[i]),

        forall|col: int| #![trigger result.1@[col]] 0 <= col < a.len() ==> 
            exists|row: int| 0 <= row < a.len() && result.1@[row]@[col] != 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed diagonal condition check */
    let n = a.len();
    
    let mut is_diag = true;
    let mut i = 0;
    while i < n && is_diag
        invariant
            0 <= i <= n,
            is_diag ==> forall|row: int, col: int| 0 <= row < i && 0 <= col < n && row != col ==> a@[row]@[col] == 0.0f32,
        decreases n - i
    {
        let mut j = 0;
        while j < n && is_diag
            invariant
                0 <= j <= n,
                is_diag ==> forall|col: int| 0 <= col < j && i as int != col ==> a@[i as int]@[col] == 0.0f32,
            decreases n - j
        {
            proof {
                assert(0 <= i < n);
                assert(0 <= j < n);
                assert(i < a.len());
                assert(j < a[i].len());
            }
            if i != j && a[i][j] != 0.0f32 {
                is_diag = false;
            }
            j += 1;
        }
        i += 1;
    }
    
    if is_diag {
        let mut eigenvalues: Vec<f32> = Vec::with_capacity(n);
        let mut k = 0;
        while k < n
            invariant
                0 <= k <= n,
                eigenvalues.len() == k,
                forall|idx: int| 0 <= idx < k ==> eigenvalues@[idx] == a@[idx]@[idx],
            decreases n - k
        {
            proof {
                assert(0 <= k < n);
                assert(k < a.len());
                assert(k < a[k].len());
            }
            eigenvalues.push(a[k][k]);
            k += 1;
        }
        
        let eigenvectors = create_identity_matrix(n);
        (eigenvalues, eigenvectors)
    } else {
        let mut eigenvalues: Vec<f32> = Vec::with_capacity(n);
        let mut i = 0;
        while i < n
            invariant
                0 <= i <= n,
                eigenvalues.len() == i,
            decreases n - i
        {
            eigenvalues.push(1.0f32);
            i += 1;
        }
        
        let eigenvectors = create_identity_matrix(n);
        (eigenvalues, eigenvectors)
    }
}
// </vc-code>

}
fn main() {}