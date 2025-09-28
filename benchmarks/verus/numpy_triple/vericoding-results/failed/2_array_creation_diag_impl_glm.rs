// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed choose statement syntax */
fn create_matrix(n: nat) -> (result: Vec<Vec<f32>>)
    ensures result@.len() == n,
           forall|i: int| 0 <= i < n ==> result@[i]@.len() == n,
           forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> result@[i]@[j] == 0.0f32,
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant 0 <= i <= n,
        result@.len() == i,
        forall|k: int| 0 <= k < i ==> result@[k]@.len() == n,
        forall|k: int| 0 <= k < i ==> forall|l: int| 0 <= l < n ==> result@[k]@[l] == 0.0f32
        decreases n - i
    {
        let mut row = Vec::new();
        let mut j = 0;
        while j < n
            invariant 0 <= j <= n,
            row@.len() == j,
            forall|l: int| 0 <= l < j ==> row@[l] == 0.0f32
            decreases n - j
        {
            row.push(0.0f32);
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}

/* helper modified by LLM (iteration 4): fixed choose statement syntax */
fn set_diagonal(matrix: &mut Vec<Vec<f32>>, v: &Vec<f32>)
    requires matrix@.len() == v@.len() > 0,
            forall|i: int| 0 <= i < matrix@.len() ==> matrix@[i]@.len() == v@.len(),
            forall|i: int, j: int| 0 <= i < matrix@.len() && 0 <= j < matrix@[i]@.len() ==> matrix@[i]@[j] == 0.0f32
    ensures matrix@.len() == v@.len(),
            forall|i: int| 0 <= i < matrix@.len() ==> matrix@[i]@.len() == v@.len(),
            forall|i: int| 0 <= i < v@.len() ==> matrix@[i]@[i] == v@[i],
            forall|i: int, j: int| 0 <= i < matrix@.len() && 0 <= j < matrix@[i]@.len() && i != j ==> matrix@[i]@[j] == 0.0f32,
            forall|i: int, j: int| 0 <= i < matrix@.len() && 0 <= j < matrix@[i]@.len() && matrix@[i]@[j] != 0.0f32 ==> i == j,
            forall|i: int, j: int| 0 <= i < matrix@.len() && 0 <= j < matrix@[i]@.len() ==> matrix@[i]@[j] == matrix@[j]@[i]
{
    let mut i = 0;
    while i < v@.len()
        invariant 0 <= i <= v@.len(),
        matrix@.len() == v@.len(),
        forall|k: int| 0 <= k < matrix@.len() ==> matrix@[k]@.len() == v@.len(),
        forall|k: int| 0 <= k < i ==> matrix@[k]@[k] == v@[k],
        forall|k: int, l: int| 0 <= k < matrix@.len() && 0 <= l < matrix@[k]@.len() && (
            (k < i && l == k) ==> matrix@[k]@[l] == v@[k],
            (k < i && l != k) || (k >= i && l != k) ==> matrix@[k]@[l] == 0.0f32,
            (k >= i && l == k) ==> matrix@[k]@[l] == 0.0f32
        ),
        forall|k: int, l: int| 0 <= k < matrix@.len() && 0 <= l < matrix@[k]@.len() && matrix@[k]@[l] != 0.0f32 ==> (
            k < i && k == l && matrix@[k]@[l] == v@[k]
        ),
        forall|k: int, l: int| 0 <= k < matrix@.len() && 0 <= l < matrix@[k]@.len() ==> matrix@[k]@[l] == matrix@[l]@[k]
        decreases v@.len() - i
    {
        matrix[i].set(i, v[i]);
        proof {
            assert forall|k: int, l: int| 0 <= k < matrix@.len() && 0 <= l < matrix@[k]@.len() && matrix@[k]@[l] != 0.0f32 implies (
                (k < i + 1 && k == l && matrix@[k]@[l] == v@[k]) ||
                (k == i && l == i && matrix@[k]@[l] == v@[k])
            ) by {
                let (k, l) = choose |(k: int, l: int)| 0 <= k < matrix@.len() && 0 <= l < matrix@[k]@.len() && matrix@[k]@[l] != 0.0f32;
                if k < i {
                    assert matrix@[k]@[l] == v@[k];
                } else if k == i {
                    assert matrix@[i]@[l] == (if l == i { v@[i] } else { 0.0f32 });
                    assert matrix@[i]@[l] != 0.0f32 ==> l == i;
                }
            };
        }
        i += 1;
    }
}
// </vc-helpers>

// <vc-spec>
fn diag(v: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires v.len() > 0,
    ensures 
        result.len() == v.len(),
        forall|i: int| 0 <= i < v@.len() ==> result@[i].len() == v@.len(),
        /* Elements on the main diagonal are from v */
        forall|i: int| 0 <= i < v@.len() ==> result@[i][i] == v@[i],
        /* All off-diagonal elements are zero */
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i != j ==> result@[i][j] == 0.0f32,
        /* Diagonal matrix property - non-zero elements only on diagonal */
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && result@[i][j] != 0.0f32 ==> i == j,
        /* The resulting matrix is symmetric */
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> result@[i][j] == result@[j][i],
        /* Each row has exactly one non-zero element at position i (unless v[i] = 0) */
        forall|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32 ==> {
            result@[i][i] != 0.0f32 && 
            forall|j: int| 0 <= j < v@.len() && j != i ==> result@[i][j] == 0.0f32
        },
        /* Each column has exactly one non-zero element at position j (unless v[j] = 0) */
        forall|j: int| 0 <= j < v@.len() && v@[j] != 0.0f32 ==> {
            result@[j][j] != 0.0f32 && 
            forall|i: int| 0 <= i < v@.len() && i != j ==> result@[i][j] == 0.0f32
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): no changes, helper functions fixed */
    let n = v.len();
    let mut result = create_matrix(n);
    set_diagonal(&mut result, &v);
    result
}
// </vc-code>


}
fn main() {}