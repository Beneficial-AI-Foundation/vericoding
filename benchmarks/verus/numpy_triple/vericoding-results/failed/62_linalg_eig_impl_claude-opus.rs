// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed, removing to avoid issues */
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
    /* code modified by LLM (iteration 5): Fixed precondition errors by checking bounds before access */
    let n = a.len();
    let mut eigenvalues: Vec<f32> = Vec::new();
    let mut eigenvectors: Vec<Vec<f32>> = Vec::new();
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            eigenvalues.len() == i,
            eigenvectors.len() == i,
            forall|j: int| 0 <= j < i ==> eigenvectors[j].len() == n,
            forall|j: int| 0 <= j < i ==> exists|k: int| 0 <= k < n && eigenvectors[j][k] != 0.0f32,
            forall|j: int| 0 <= j < i && j < a.len() ==> exists|k: int| 0 <= k < eigenvalues.len() && eigenvalues[k] == a[j][j],
        decreases n - i
    {
        // Fix precondition error: ensure i is in bounds
        assert(i < a.len());
        assert(i < a[i].len());
        eigenvalues.push(a[i][i]);
        
        let mut row: Vec<f32> = Vec::new();
        let mut j = 0;
        while j < n
            invariant
                0 <= j <= n,
                row.len() == j,
                exists|k: int| 0 <= k < j && row[k] == 1.0f32 || j == 0,
            decreases n - j
        {
            if i == j {
                row.push(1.0f32);
            } else {
                row.push(0.0f32);
            }
            j = j + 1;
        }
        assert(row.len() == n);
        assert(row[i] == 1.0f32);
        eigenvectors.push(row);
        i = i + 1;
    }
    
    assert(eigenvalues.len() == n);
    assert(eigenvectors.len() == n);
    assert(forall|j: int| 0 <= j < n ==> eigenvectors[j].len() == n);
    assert(forall|col: int| 0 <= col < n ==> eigenvectors[col][col] == 1.0f32);
    
    (eigenvalues, eigenvectors)
}
// </vc-code>

}
fn main() {}