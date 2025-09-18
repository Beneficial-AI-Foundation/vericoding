// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): integer conversion */
spec fn nat_to_int(i: nat) -> int { i as int }

/* helper modified by LLM (iteration 5): check index within length */
spec fn within_len(len: nat, i: int) -> bool { 0 <= i && i < len as int }
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
    /* code modified by LLM (iteration 5): implement tril creating lower-triangular copy with proper invariants */
    let n: nat = m.len();
    let cols: nat = m[0].len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let k_int: int = k as int;

    let mut i: nat = 0;
    while i < n
        invariant result.len() == i,
        invariant forall |p: nat| p < i ==> result[p].len() == cols,
        invariant forall |p: nat, q: nat| p < i && q < cols ==> result[p][q] == if (p as int) >= (q as int) - k_int { m[p][q] } else { 0.0 },
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: nat = 0;
        while j < cols
            invariant row.len() == j,
            invariant forall |q: nat| q < j ==> row[q] == if (i as int) >= (q as int) - k_int { m[i][q] } else { 0.0 },
            decreases cols - j
        {
            let val: f64 = if (i as int) >= (j as int) - k_int { m[i][j] } else { 0.0 };
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