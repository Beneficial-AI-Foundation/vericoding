// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn diag_val(i: int, j: int) -> (result: f64)
    ensures
        result == if i == j { 1.0 } else { 0.0 },
{
    if i == j { 1.0 } else { 0.0 }
}
// </vc-helpers>

// <vc-spec>
fn identity(n: usize) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            result[i][j] == if i == j { 1.0 } else { 0.0 }
// </vc-spec>
// <vc-code>
{
    let mut mat: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            mat.len() == i,
            i <= n,
            forall|k: int| 0 <= k < i ==> mat[k].len() == n,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < n ==> mat[k][j] == if k == j { 1.0 } else { 0.0 },
        decreases (n - i) as int
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                row.len() == j,
                j <= n,
                forall|m: int| 0 <= m < j ==> row[m] == if m == i as int { 1.0 } else { 0.0 },
            decreases (n - j) as int
        {
            let v: f64 = if j == i { 1.0 } else { 0.0 };
            row.push(v);
            j = j + 1;
        }
        mat.push(row);
        i = i + 1;
    }
    mat
}
// </vc-code>

}
fn main() {}