// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added decreases clause to loop */
spec fn spec_row(n: nat, diag_index: int) -> Seq<f64> {
    Seq::new(n, |j: int| if j == diag_index { 1.0 } else { 0.0 })
}

fn create_row(n: usize, diag_index: usize) -> (row: Vec<f64>)
    requires
        diag_index < n,
    ensures
        row.len() == n,
        row@ == spec_row(n as nat, diag_index as int),
{
    let mut row = Vec::with_capacity(n);
    let mut j: usize = 0;
    while j < n
        invariant
            0 <= j <= n,
            diag_index < n,
            row.len() == j,
            forall|k: int| 0 <= k < j ==> row@[k] == if k == diag_index as int { 1.0 } else { 0.0 }
        decreases n - j
    {
        if j == diag_index {
            row.push(1.0);
        } else {
            row.push(0.0);
        }
        j = j + 1;
    }
    row
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
    /* code modified by LLM (iteration 3): added decreases clause to loop */
    let mut result: Vec<Vec<f64>> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == n,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < n ==> result[k][l] == if k == l { 1.0 } else { 0.0 }
        decreases n - i
    {
        let row = create_row(n, i);
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}