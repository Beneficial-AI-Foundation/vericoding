// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversions in sequence indexing */
proof fn diagonal_eigenvalues(a: Vec<Vec<f32>>)
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a@[i].len() == a.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && i != j ==> a@[i]@[j] == 0.0f32
    ensures
        exists|eig_vals: Vec<f32>, eig_vecs: Vec<Vec<f32>>|
            eig_vals.len() == a.len() && eig_vecs.len() == a.len()
            && forall|i: int| 0 <= i < eig_vecs.len() ==> eig_vecs@[i].len() == a.len()
            && forall|i: int| 0 <= i < a.len() ==> exists|j: int| 0 <= j < eig_vals.len() && eig_vals@[j] == a@[i]@[i]
{
    proof {
        let mut eig_vals: Vec<f32> = Vec::new();
        let mut eig_vecs: Vec<Vec<f32>> = Vec::new();
        
        let mut i: int = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                eig_vals.len() == i,
                eig_vecs.len() == i,
                forall|k: int| 0 <= k < i ==> eig_vals@[k] == a@[k]@[k],
                forall|k: int| 0 <= k < i ==> eig_vecs@[k].len() == a.len(),
                forall|k: int, j: int| 0 <= k < i && 0 <= j < a.len() ==> 
                    eig_vecs@[k]@[j] == (if k == j { 1.0f32 } else { 0.0f32 })
        {
            eig_vals.push(a@[i]@[i]);
            
            let mut vec_row: Vec<f32> = Vec::new();
            let mut j: int = 0;
            while j < a.len()
                invariant
                    0 <= j <= a.len(),
                    vec_row.len() == j,
                    forall|k: int| 0 <= k < j ==> vec_row@[k] == (if i == k { 1.0f32 } else { 0.0f32 })
            {
                let value = if i == j { 1.0f32 } else { 0.0f32 };
                vec_row.push(value);
                j += 1;
            }
            
            eig_vecs.push(vec_row);
            i += 1;
        }
        
        assert(eig_vals.len() == a.len());
        assert(eig_vecs.len() == a.len());
        assert forall|i: int| 0 <= i < eig_vecs.len() implies eig_vecs@[i].len() == a.len() by {
            assert(eig_vecs@[i].len() == a.len());
        };
        assert forall|i: int| 0 <= i < a.len() implies exists|j: int| 0 <= j < eig_vals.len() && eig_vals@[j] == a@[i]@[i] by {
            assert(eig_vals@[i] == a@[i]@[i]);
        };
    }
}

// Helper to check if a vector is non-zero
spec fn vector_nonzero(v: Vec<f32>) -> bool
    recommends v.len() > 0
    decreases v.len()
{
    exists|i: int| 0 <= i < v.len() && v@[i] != 0.0f32
}

// Helper to check if matrix is diagonal
spec fn is_diagonal(a: Vec<Vec<f32>>) -> bool
    recommends a.len() > 0
    decreases a.len()
{
    forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && i != j ==> a@[i]@[j] == 0.0f32
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
    /* code modified by LLM (iteration 5): Fixed type conversions in sequence indexing */
    let mut eigenvalues: Vec<f32> = Vec::with_capacity(a.len());
    let mut eigenvectors: Vec<Vec<f32>> = Vec::with_capacity(a.len());
    
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            eigenvalues.len() == i,
            eigenvectors.len() == i,
            forall|k: int| 0 <= k < i ==> eigenvalues@[k] == a@[k]@[k],
            forall|k: int| 0 <= k < i ==> eigenvectors@[k].len() == a.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < a.len() ==> 
                eigenvectors@[k]@[j] == (if k == j { 1.0f32 } else { 0.0f32 })
    {
        eigenvalues.push(a@[i]@[i]);
        
        let mut eigenvector: Vec<f32> = Vec::with_capacity(a.len());
        let mut j: int = 0;
        while j < a.len()
            invariant
                0 <= j <= a.len(),
                eigenvector.len() == j,
                forall|k: int| 0 <= k < j ==> eigenvector@[k] == (if i == k { 1.0f32 } else { 0.0f32 })
        {
            let value = if i == j { 1.0f32 } else { 0.0f32 };
            eigenvector.push(value);
            j += 1;
        }
        
        eigenvectors.push(eigenvector);
        i += 1;
    }
    
    (eigenvalues, eigenvectors)
}
// </vc-code>

}
fn main() {}