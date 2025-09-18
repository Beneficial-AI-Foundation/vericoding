// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_transpose(a: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        a.len() > 0,
        forall|i: int| #![trigger a[i]] 0 <= i < a.len() ==> a[i].len() == a[0].len(),
        a[0].len() > 0,
    ensures
        result.len() == a[0].len(),
        forall|j: int| #![trigger result[j]] 0 <= j < result.len() ==> result[j].len() == a.len(),
        forall|i: int, j: int| #![trigger result[j][i]]
            0 <= i < a.len() && 0 <= j < a[0].len() ==> 
            result[j][i] == a[i][j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clauses to both while loops to prove termination. */
    let m = a.len();
    let n = a[0].len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            m == a.len(),
            n == a[0].len(),
            forall|i: int| #![trigger a[i]] 0 <= i < (m as int) ==> a[i].len() == n,
            0 <= j <= n,
            result.len() == j,
            forall|k: int| #![trigger result[k]] 0 <= k < (j as int) ==> result[k].len() == m,
            forall|k: int, l: int| #![trigger result[k][l]] 0 <= k < (j as int) && 0 <= l < (m as int) ==> result[k][l] == a[l][k],
        decreases n - j
    {
        let mut new_row: Vec<f32> = Vec::new();
        let mut i: usize = 0;
        while i < m
            invariant
                m == a.len(),
                n == a[0].len(),
                forall|k: int| #![trigger a[k]] 0 <= k < (m as int) ==> a[k].len() == n,
                0 <= j < n,
                0 <= i <= m,
                new_row.len() == i,
                forall|l: int| #![trigger new_row[l]] 0 <= l < (i as int) ==> new_row[l] == a[l][j as int],
            decreases m - i
        {
            new_row.push(a[i][j]);
            i = i + 1;
        }
        result.push(new_row);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}