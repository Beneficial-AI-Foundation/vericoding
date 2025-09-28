// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): resubmitting helper function */
fn make_eigenvector_row(n: usize, i: usize) -> (res: Vec<f32>)
    requires
        i < n,
    ensures
        res.len() == n,
        forall|j: int| 0 <= j < n ==> 
            if j == i { res@[j] == 1.0f32 } else { res@[j] == 0.0f32 },
{
    let mut row = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            i < n,
            row.len() == j,
            forall|k: int| 0 <= k < j ==> 
                if k == i { row@[k] == 1.0f32 } else { row@[k] == 0.0f32 },
        decreases n - j,
    {
        if j == i {
            row.push(1.0f32);
        } else {
            row.push(0.0f32);
        }
        j = j + 1;
    }
    row
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
    /* code modified by LLM (iteration 5): added triggers to forall assertions */
    let n = a.len();
    let mut eigenvalues: Vec<f32> = Vec::new();
    let mut eigenvectors: Vec<Vec<f32>> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            a.len() == n,
            forall|k: int| 0 <= k < a.len() ==> a@[k].len() == a.len(),
            eigenvalues.len() == i,
            eigenvectors.len() == i,
            forall|k: int| 0 <= k < i ==> eigenvalues@[k] == a@[k]@[k],
            forall|k: int| 0 <= k < i ==> eigenvectors@[k].len() == n,
            forall|k: int, j: int|
                0 <= k < i && 0 <= j < n ==> 
                    if j == k { eigenvectors@[k]@[j] == 1.0f32 } else { eigenvectors@[k]@[j] == 0.0f32 },
        decreases n - i,
    {
        eigenvalues.push(a[i][i]);
        let eigenvector_row = make_eigenvector_row(n, i);
        eigenvectors.push(eigenvector_row);
        i = i + 1;
    }

    proof {
        assert forall|idx: int| #![trigger a@[idx]] 0 <= idx < n implies
            (exists|j: int| 0 <= j < eigenvalues.len() && eigenvalues@[j] == a@[idx]@[idx])
        by {
            assert(eigenvalues@[idx] == a@[idx]@[idx]);
        }

        assert forall|col: int| #![trigger eigenvectors@[col]] 0 <= col < n implies
            (exists|row: int| 0 <= row < n && eigenvectors@[row]@[col] != 0.0f32)
        by {
            assert(eigenvectors@[col]@[col] == 1.0f32);
        }
    }
    
    (eigenvalues, eigenvectors)
}
// </vc-code>

}
fn main() {}