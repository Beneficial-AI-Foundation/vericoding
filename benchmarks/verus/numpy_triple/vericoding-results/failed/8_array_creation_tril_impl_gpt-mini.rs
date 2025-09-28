// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate usize and int bounds for indices */
fn usize_int_relations(len: usize, idx: usize)
    requires
        idx < len,
    ensures
        (idx as int) < (len as int),
{
    ()
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
{
    /* code modified by LLM (iteration 5): implement tril by building rows with proper bounds and asserts */
    let n = m.len();
    let mcols = m[0].len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            result.len() == i,
            forall|r: int, c: int|
                0 <= r < i as int && 0 <= c < mcols as int ==> #[trigger] result[r][c] == if r >= c - (k as int) { m[r][c] } else { 0.0 },
        decreases (n as int) - (i as int)
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < mcols
            invariant
                0 <= j as int,
                j as int <= mcols as int,
                row.len() == j,
                forall|c: int|
                    0 <= c < j as int ==> #[trigger] row[c] == if i as int >= c - (k as int) { m[i as int][c] } else { 0.0 },
            decreases (mcols as int) - (j as int)
        {
            assert(i < n);
            assert(j < mcols);
            let val: f64 = if (i as int) >= (j as int) - (k as int) { m[i][j] } else { 0.0 };
            row.push(val);
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