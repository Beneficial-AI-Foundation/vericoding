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
/* code modified by LLM (iteration 5): replaced int with isize in condition to fix compilation error */
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    let n = m.len();
    let p = m[0].len();

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            result.len() == i,
            forall|row: int| 0 <= row < i as int ==> #[trigger] result@[row].len() == p,
            forall|row: int, col: int| 
                0 <= row < i as int && 0 <= col < p as int ==> 
                #[trigger] result@[row]@[col] == if row >= col - (k as int) { m@[row]@[col] } else { 0.0 },
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < p
            invariant
                0 <= j as int <= p as int,
                row.len() == j,
                forall|col: int| 0 <= col < j as int ==> 
                    #[trigger] row@[col] == if (i as int) >= col - (k as int) { m@[(i as int)]@[col] } else { 0.0 },
            decreases p - j
        {
            let val = if (i as isize) >= (j as isize) - (k as isize) { m[i][j] } else { 0.0 };
            row.push(val);
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