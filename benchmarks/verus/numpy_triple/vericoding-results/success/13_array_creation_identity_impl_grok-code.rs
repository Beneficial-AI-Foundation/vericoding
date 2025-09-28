// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i as int,
            forall|k: int| 0 <= k < i ==> result[k].len() == n,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < n ==>
                result[k][l] == if k == l { 1.0 } else { 0.0 },
        decreases n - i,
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                row.len() == j as int,
                forall|l: int| 0 <= l < j ==>
                    row[l] == if i == l { 1.0 } else { 0.0 },
            decreases n - j,
        {
            row.push(if i == j { 1.0 } else { 0.0 });
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}