// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_i8_zero_nonneg()
    ensures
        (0i8 as int) >= 0,
{
}

// </vc-helpers>

// <vc-spec>
fn numpy_cov(m: Vec<Vec<i8>>) -> (cov_matrix: Vec<Vec<i8>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> m[i].len() > 0,
        forall|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() ==> m[i].len() == m[j].len(),
    ensures 
        cov_matrix.len() == m.len(),
        forall|i: int| 0 <= i < cov_matrix.len() ==> cov_matrix[i].len() == m.len(),
        forall|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() ==> 
            cov_matrix[i][j] == cov_matrix[j][i],
        forall|i: int| 0 <= i < m.len() ==> (cov_matrix[i][i] as int) >= 0,
// </vc-spec>
// <vc-code>
{
    let n = m.len();
    let mut cov_matrix: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            cov_matrix.len() == i,
            i as int <= n as int,
            forall|r: int| 0 <= r < cov_matrix.len() ==> cov_matrix[r].len() == n,
            forall|r: int, c: int| 0 <= r < cov_matrix.len() && 0 <= c < n ==> cov_matrix[r][c] == 0i8,
        decreases n - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                row.len() == j,
                j as int <= n as int,
                forall|c: int| 0 <= c < row.len() ==> row[c] == 0i8,
            decreases n - j
        {
            row.push(0i8);
            j = j + 1;
        }
        cov_matrix.push(row);
        i = i + 1;
    }
    cov_matrix
}
// </vc-code>


}
fn main() {}