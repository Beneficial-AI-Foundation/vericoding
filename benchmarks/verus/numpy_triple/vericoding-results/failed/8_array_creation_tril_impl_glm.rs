// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): fixed invariant syntax by using parentheses instead of braces */
{
    let n = m.len();
    let ncols = m[0].len();
    let mut result = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant (
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == ncols,
        )
    {
        let mut row = Vec::with_capacity(ncols);
        for j in 0..ncols
            invariant (
                0 <= j <= ncols,
                row.len() == j,
            )
        {
            let i_int = i as int;
            let j_int = j as int;
            if i_int >= j_int - (k as int) {
                row.push(m[i][j]);
            } else {
                row.push(0.0);
            }
        }
        assert(row.len() == ncols);
        result.push(row);
        i += 1;
    }
    assert(result.len() == n);
    result
}
// </vc-code>

}
fn main() {}