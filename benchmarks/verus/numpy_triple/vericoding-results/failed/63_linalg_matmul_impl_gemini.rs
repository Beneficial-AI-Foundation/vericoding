// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added assert with proof block */
fn dot_product_row_col(row: &Vec<f32>, B: &Vec<Vec<f32>>, j: usize) -> (sum: f32)
    requires
        B.len() > 0,
        row.len() == B.len(),
        (j as int) < B@[0].len(),
        forall|i: int| 0 <= i < B.len() ==> #[trigger] B@[i].len() == B@[0].len(),
{
    let p = row.len();
    let mut sum = 0.0f32;
    let mut k: usize = 0;
    while k < p
        invariant
            0 <= k <= p,
            row.len() == p,
            B.len() == p,
            (j as int) < B@[0].len(),
            forall|i: int| 0 <= i < B.len() ==> #[trigger] B@[i].len() == B@[0].len(),
        decreases p - k
    {
        assert(B[k].len() == B[0].len()) by {};
        sum = sum + row[k] * B[k][j];
        k = k + 1;
    }
    sum
}

/* helper modified by LLM (iteration 3): added decreases clause to loop */
fn compute_row(row_A: &Vec<f32>, B: &Vec<Vec<f32>>) -> (res_row: Vec<f32>)
    requires
        B.len() > 0,
        row_A.len() == B.len(),
        forall|i: int| 0 <= i < B.len() ==> #[trigger] B@[i].len() == B@[0].len(),
    ensures
        res_row.len() == B@[0].len(),
{
    let n = B[0].len();
    let mut res_row = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            0 <= j <= n,
            res_row.len() == j,
            row_A.len() == B.len(),
            B.len() > 0,
            n == B@[0].len(),
            forall|i: int| 0 <= i < B.len() ==> #[trigger] B@[i].len() == n,
        decreases n - j
    {
        let val = dot_product_row_col(row_A, B, j);
        res_row.push(val);
        j = j + 1;
    }
    res_row
}
// </vc-helpers>

// <vc-spec>
fn matmul(A: Vec<Vec<f32>>, B: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires
        A.len() > 0,
        B.len() > 0,
        A@[0].len() == B.len(),
        forall|i: int| 0 <= i < A.len() ==> #[trigger] A@[i].len() == A@[0].len(),
        forall|i: int| 0 <= i < B.len() ==> #[trigger] B@[i].len() == B@[0].len(),
    ensures
        result.len() == A.len(),
        result.len() > 0 ==> result@[0].len() == B@[0].len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result@[i].len() == B@[0].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added assert with proof block */
    let m = A.len();
    let n = B[0].len();

    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            0 <= i <= m,
            A.len() == m,
            B.len() > 0,
            n == B@[0].len(),
            A@[0].len() == B.len(),
            forall|k: int| 0 <= k < A.len() ==> #[trigger] A@[k].len() == A@[0].len(),
            forall|k: int| 0 <= k < B.len() ==> #[trigger] B@[k].len() == B@[0].len(),
            result.len() == i,
            forall|x: int| 0 <= x < i ==> #[trigger] result@[x].len() == n,
        decreases m - i
    {
        assert(A[i].len() == B.len()) by {};
        let row = compute_row(&A[i], &B);
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}