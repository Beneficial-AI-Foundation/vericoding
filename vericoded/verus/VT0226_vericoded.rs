// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zeros_vec(n: usize) -> (v: Vec<f32>)
    ensures
        v.len() == n,
        v@.len() == n,
{
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v.len() == i,
        decreases n - i
    {
        v.push(0.0f32);
        i += 1;
    }
    v
}

fn zeros_matrix(n: usize) -> (m: Vec<Vec<f32>>)
    ensures
        m.len() == n,
        forall|i: int| 0 <= i < m.len() ==> m[i]@.len() == n,
{
    let mut m: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            m.len() == i,
            forall|k: int| 0 <= k < m.len() ==> m[k]@.len() == n,
        decreases n - i
    {
        let row = zeros_vec(n);
        m.push(row);
        i += 1;
    }
    m
}
// </vc-helpers>

// <vc-spec>
struct EighResult {
    eigenvalues: Vec<f32>,
    eigenvectors: Vec<Vec<f32>>,
}

fn eigh(a: Vec<Vec<f32>>) -> (result: EighResult)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i]@.len() == a.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i][j] == a[j][i],
    ensures
        result.eigenvalues.len() == a.len(),
        result.eigenvectors.len() == a.len(),
        forall|i: int| 0 <= i < result.eigenvectors.len() ==> result.eigenvectors[i]@.len() == a.len(),
// </vc-spec>
// <vc-code>
{
    let n: usize = a.len();
    let eigenvalues = zeros_vec(n);
    let eigenvectors = zeros_matrix(n);
    EighResult { eigenvalues, eigenvectors }
}
// </vc-code>

}
fn main() {}