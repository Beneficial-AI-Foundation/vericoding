// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added decreases clauses and fixed invariant syntax */
fn dot_product(row: &Vec<i8>, col: &Vec<i8>) -> (res: i8)
    requires
        row.len() == col.len(),
{
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < row.len()
        invariant
            0 <= i <= row.len(),
        decreases row.len() - i
    {
        let prod = (row[i] as i64) * (col[i] as i64);
        sum = sum + prod;
        i = i + 1;
    }
    sum as i8
}

/* helper modified by LLM (iteration 4): Added decreases clauses and fixed invariant syntax */
fn get_col(m: &Vec<Vec<i8>>, j: usize) -> (col: Vec<i8>)
    requires
        m.len() > 0,
        j < m@[0].len(),
        forall|i: int| 0 <= i < m.len() ==> #[trigger] m@[i].len() == m@[0].len(),
    ensures
        col.len() == m.len(),
        forall|i: int| 0 <= i < m.len() ==> col@[i] == m@[i]@[j as int],
{
    let mut col: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < m.len()
        invariant
            0 <= i <= m.len(),
            col.len() == i,
            forall|k: int| 0 <= k < i ==> col@[k] == m@[k]@[j as int],
        decreases m.len() - i
    {
        col.push(m[i][j]);
        i = i + 1;
    }
    col
}
// </vc-helpers>

// <vc-spec>
fn matmul(A: Vec<Vec<i8>>, B: Vec<Vec<i8>>) -> (result: Vec<Vec<i8>>)
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
    /* code modified by LLM (iteration 4): Added decreases clauses to prove termination. */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < A.len()
        invariant
            0 <= i <= A.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k].len() == B@[0].len(),
        decreases A.len() - i
    {
        let mut new_row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < B[0].len()
            invariant
                i < A.len(),
                0 <= j <= B[0].len(),
                new_row.len() == j,
            decreases B[0].len() - j
        {
            let col_b = get_col(&B, j);
            let val = dot_product(&A[i], &col_b);
            new_row.push(val);
            j = j + 1;
        }
        result.push(new_row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}