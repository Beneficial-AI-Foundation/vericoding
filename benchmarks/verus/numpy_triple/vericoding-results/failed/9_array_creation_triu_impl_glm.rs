// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn triu(m: &Vec<Vec<f32>>, k: i8) -> (result: Vec<Vec<f32>>)
    requires 
        m@.len() > 0,
        forall|i: int| 0 <= i < m@.len() ==> #[trigger] m@[i].len() == m@[0].len(),
    ensures
        result@.len() == m@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i].len() == m@[i].len(),
        forall|i: int, j: int| 
            0 <= i < result@.len() && 0 <= j < result@[i].len() ==>
            #[trigger] result@[i][j] == if i > j - k as int { 0.0f32 } else { m@[i][j] },
        forall|i: int, j: int|
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i <= j - k as int ==>
            #[trigger] result@[i][j] == m@[i][j],
        forall|i: int, j: int|
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i > j - k as int ==>
            #[trigger] result@[i][j] == 0.0f32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): simplified condition using integer arithmetic and converted loops to while with invariants */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < m.len()
        invariant
            0 <= i <= m@.len(),
            result@.len() == i,
            forall|idx: int| 0 <= idx < i ==> #[trigger] result@[idx].len() == m@[idx].len(),
    {
        let mut row = Vec::new();
        let inner_len = m[i].len();
        let mut j = 0;
        while j < inner_len
            invariant
                0 <= j <= inner_len,
                row@.len() == j,
        {
            let condition = (i as int) > (j as int) - (k as int);
            if condition {
                row.push(0.0f32);
            } else {
                row.push(m[i][j]);
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