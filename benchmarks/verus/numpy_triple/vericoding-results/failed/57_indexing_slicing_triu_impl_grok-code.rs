// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): added decreases clauses to both loops to fix verification termination requirement */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < m.len()
        decreases m.len() - i
        invariant
            i <= m.len(),
            result.len() == i,
            forall|ii: int| 0 <= ii < i ==> result@[ii].len() == m@[0].len(),
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < result@[ii].len() && #[verifier::truncate] (ii as i32) + k <= #[verifier::truncate] (jj as i32) ==> result@[ii]@[jj] == m@[ii]@[jj],
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < result@[ii].len() && #[verifier::truncate] (ii as i32) + k > #[verifier::truncate] (jj as i32) ==> result@[ii]@[jj] == 0.0,
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < m[0].len()
            decreases m[0].len() - j
            invariant
                j <= m[0].len(),
                row.len() == j,
                forall|jj: int| 0 <= jj < j && #[verifier::truncate] (i as i32) + k <= #[verifier::truncate] (jj as i32) ==> row@[jj] == m@[(i as int)]@[jj],
                forall|jj: int| 0 <= jj < j && #[verifier::truncate] (i as i32) + k > #[verifier::truncate] (jj as i32) ==> row@[jj] == 0.0,
        {
            if #[verifier::truncate] (i as i32) + k <= #[verifier::truncate] (j as i32) {
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