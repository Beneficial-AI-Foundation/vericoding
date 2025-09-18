// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): returns number of columns for non-empty matrix */
spec fn ncols_usize(m: Vec<Vec<f64>>) -> usize { m[0].len() }
// </vc-helpers>

// <vc-spec>
fn triu(m: Vec<Vec<f64>>, k: i32) -> (result: Vec<Vec<f64>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> #[trigger] m[i].len() == m[0].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == m[0].len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() && (i as i32) + k <= (j as i32) ==> #[trigger] result[i][j] == m[i][j],
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() && (i as i32) + k > (j as i32) ==> #[trigger] result[i][j] == 0.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result with nested while loops and invariants to prove lengths and element values */
    let nrows: usize = m.len();
    let ncols: usize = m[0].len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < nrows
        invariant i <= nrows;
        invariant result.len() == i;
        invariant forall|t: int| 0 <= t < result.len() ==> result[t].len() == ncols;
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < ncols
            invariant j <= ncols;
            invariant row.len() == j;
        {
            proof {
                assert(i < nrows);
                assert(j < ncols);
                assert(m[i].len() == ncols);
                assert(j < m[i].len());
            }
            if (i as i32) + k <= (j as i32) {
                row.push(m[i][j]);
            } else {
                row.push(0.0);
            }
            j = j + 1;
        }
        proof {
            assert(row.len() == ncols);
        }
        result.push(row);
        i = i + 1;
    }
    proof {
        assert(result.len() == nrows);
        let mut ii: usize = 0;
        while ii < result.len()
            invariant ii <= result.len();
        {
            assert(result[ii].len() == ncols);
            ii = ii + 1;
        }
    }
    result
}
// </vc-code>

}
fn main() {}