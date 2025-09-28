// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Added Vec2D type alias and fixed index conversions */
type Vec2D = Vec<Vec<f64>>;

spec fn zero_f64() -> f64 {
    0.0
}

spec fn should_be_zero(i: int, j: int, k: int) -> bool {
    i + k > j
}

proof fn vec_len_preserved<T>(v: Vec<T>)
    ensures
        v@.len() == v.len(),
{
}

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
    /* code modified by LLM (iteration 5): Fixed type annotations and array indexing */
    let m_inner_len = m[0].len();
    let n = m.len();
    let mut result: Vec2D = Vec::new();
    let mut i: usize = 0;
    while i < m.len()
        invariant
            i <= m.len(),
            result.len() == i,
            forall|row_idx: int| 0 <= row_idx < i ==> #[trigger] result@[row_idx].len() == m_inner_len,
            forall|row_idx: int, col_idx: int| 0 <= row_idx < i && 0 <= col_idx < m_inner_len ==> {
                let k_val = k as int;
                let keep_value = row_idx + k_val <= col_idx;
                result@[row_idx][col_idx] == if keep_value { m@[row_idx][col_idx] } else { zero_f64() }
            },
    {
        let mut row = Vec::new();
        let mut j: usize = 0;
        while j < m_inner_len
            invariant
                j <= m_inner_len,
                row.len() == j,
                forall|col_idx: int| 0 <= col_idx < j ==> {
                    let k_val = k as int;
                    let keep_value = i as int + k_val <= col_idx;
                    row@[col_idx] == if keep_value { m@[i][col_idx] } else { zero_f64() }
                },
        {
            if i as int + k as int <= j as int {
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