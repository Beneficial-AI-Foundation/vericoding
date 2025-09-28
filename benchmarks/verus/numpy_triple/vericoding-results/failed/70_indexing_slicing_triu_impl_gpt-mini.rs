// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): return zero for f64 */
fn zero_f64() -> f64 { 0.0 }

/* helper modified by LLM (iteration 5): convert i8 to int for specs */
spec fn k_to_int(k: i8) -> int { k as int }
// </vc-helpers>

// <vc-spec>
fn triu(m: Vec<Vec<f64>>, k: i8) -> (result: Vec<Vec<f64>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m@.len() ==> #[trigger] m@[i].len() == m@[0].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i].len() == m@[0].len(),
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() && i + (k as int) <= j ==> #[trigger] result@[i][j] == m@[i][j],
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() && i + (k as int) > j ==> #[trigger] result@[i][j] == 0.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement triu with int indices and proper casts */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: int = 0;
    while i < m@.len()
        invariant
            result@.len() == i,
            0 <= i && i <= m@.len(),
        decreases m@.len() - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: int = 0;
        while j < m@[0].len()
            invariant
                row@.len() == j,
                0 <= j && j <= m@[0].len(),
            decreases m@[0].len() - j
        {
            #[verifier::truncate]
            let iu: usize = i as usize;
            #[verifier::truncate]
            let ju: usize = j as usize;
            let keep = j >= i + (k as int);
            if keep {
                let val = m[iu][ju];
                row.push(val);
            } else {
                row.push(zero_f64());
            }
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