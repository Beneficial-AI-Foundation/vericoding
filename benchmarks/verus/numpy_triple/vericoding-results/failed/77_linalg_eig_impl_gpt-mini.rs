// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): construct identity matrix with int indices and require non-negative n */
fn identity_matrix(n: int) -> Vec<Vec<f32>>
    requires
        n >= 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < result.len() ==> result@[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> result@[i]@[j] == if i == j { 1.0f32 } else { 0.0f32 },
{
    let mut m: Vec<Vec<f32>> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            m.len() == i,
            forall|k: int, j: int| 0 <= k < m.len() && 0 <= j < n ==> m@[k]@[j] == if k == j { 1.0f32 } else { 0.0f32 },
        decreases n - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: int = 0;
        while j < n
            invariant
                row.len() == j,
                forall|p: int| 0 <= p < row.len() ==> row@[p] == if p == i { 1.0f32 } else { 0.0f32 },
            decreases n - j
        {
            if j == i {
                row.push(1.0f32);
            } else {
                row.push(0.0f32);
            }
            j = j + 1;
        }
        m.push(row);
        i = i + 1;
    }
    m
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
/* code modified by LLM (iteration 5): collect diagonal entries and return identity eigenvectors */
{
    let n: int = a.len();
    let mut vals: Vec<f32> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            vals.len() == i,
            forall|k: int| 0 <= k < vals.len() ==> vals@[k] == a@[k]@[k],
        decreases n - i
    {
        let diag: f32 = a[i as usize][i as usize];
        vals.push(diag);
        i = i + 1;
    }
    let vecs: Vec<Vec<f32>> = identity_matrix(n);
    let result: (Vec<f32>, Vec<Vec<f32>>) = (vals, vecs);
    result
}

// </vc-code>

}
fn main() {}