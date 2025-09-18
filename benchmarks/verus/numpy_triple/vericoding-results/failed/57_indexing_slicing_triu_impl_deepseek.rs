// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversion in helper function */
proof fn lemma_vec_len_consistent<T>(m: &Vec<Vec<T>>) 
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> #[trigger] m[i].len() == m[0].len()
    ensures 
        forall|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() ==> m[i].len() == m[j].len()
{
}

spec fn is_triu_index(i: int, j: int, k: i32) -> bool {
    (i as i32) + k <= (j as i32)
}
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
/* code modified by LLM (iteration 5): Fixed integer type conversion in access expression */
{
    let mut result = Vec::<Vec<f64>>::new();
    let n = m.len();
    let inner_len = m[0].len();
    
    proof { lemma_vec_len_consistent(&m); }
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|r: int| 0 <= r < i ==> #[trigger] result[r].len() == inner_len,
            forall|r: int, c: int| 0 <= r < i && 0 <= c < inner_len && is_triu_index(r, c, k) ==> #[trigger] result[r][c] == m@[r][c],
            forall|r: int, c: int| 0 <= r < i && 0 <= c < inner_len && !is_triu_index(r, c, k) ==> #[trigger] result[r][c] == 0.0
    {
        let mut row = Vec::<f64>::new();
        let mut j: usize = 0;
        while j < inner_len
            invariant
                j <= inner_len,
                row.len() == j,
                forall|c: int| 0 <= c < j && is_triu_index(i as int, c as int, k) ==> #[trigger] row[c] == m@[i][c as int],
                forall|c: int| 0 <= c < j && !is_triu_index(i as int, c as int, k) ==> #[trigger] row[c] == 0.0
        {
            if (i as i32) + k <= (j as i32) {
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