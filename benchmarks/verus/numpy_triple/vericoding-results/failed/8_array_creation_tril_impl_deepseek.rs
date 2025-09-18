// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Convert index comparisons to use natural numbers */
fn compare_indices(i: nat, j: nat, k: i32) -> bool 
    ensures result == (i >= j - (k as int))
{
    if k >= 0 {
        i >= j - (k as nat)
    } else {
        i + (-k) as nat >= j
    }
}
// </vc-helpers>

// <vc-spec>
fn tril(m: Vec<Vec<f64>>, k: i32) -> (result: Vec<Vec<f64>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> #[trigger] m[i].len() == m[0].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == m[0].len(),
        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            #[trigger] result[i][j] == if i >= j - k { m[i][j] } else { 0.0 },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use helper function and proper integer/nat conversion */
{
    let n = m.len();
    let cols = m[0].len();
    let mut result = Vec::<Vec<f64>>::new();
    let mut i: usize = 0;
    while i < n 
        invariant 
            i <= n,
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> #[trigger] result[idx].len() == cols,
            forall|idx: int, jdx: int| 
                0 <= idx < i && 0 <= jdx < cols ==> 
                #[trigger] result[idx][jdx] == if compare_indices(idx as nat, jdx as nat, k) { m[idx][jdx as usize] } else { 0.0 }
    {
        let mut row = Vec::<f64>::new();
        let mut j: usize = 0;
        while j < cols 
            invariant 
                j <= cols,
                row.len() == j,
                forall|jdx: int| 0 <= jdx < j ==> 
                    #[trigger] row[jdx] == if compare_indices(i as nat, jdx as nat, k) { m[i][jdx as usize] } else { 0.0 }
        {
            if compare_indices(i as nat, j as nat, k) {
                row.push(m[i][j]);
            } else {
                row.push(0.0);
            }
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}