// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): row-length equality from precondition */
proof fn lemma_rows_have_same_len(m: Seq<Seq<f32>>, i: int)
    requires
        m.len() > 0,
        forall|p: int| 0 <= p < m.len() ==> #[trigger] m[p].len() == m[0].len(),
        0 <= i < m.len(),
    ensures
        m[i].len() == m[0].len(),
{
    assert(forall|p: int| 0 <= p < m.len() ==> #[trigger] m[p].len() == m[0].len());
    assert(m[i].len() == m[0].len());
}

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
{
    /* code modified by LLM (iteration 5): simplified condition using int arithmetic to match spec directly */
    let mut res: Vec<Vec<f32>> = Vec::new();
    let m_len = m.len();
    let mut i: usize = 0;
    while i < m_len
        invariant
            m@.len() > 0,
            m_len == m.len(),
            i <= m_len,
            res@.len() == i as int,
            forall|p: int| 0 <= p < res@.len() ==> #[trigger] res@[p].len() == m@[p].len(),
            forall|p: int, q: int|
                0 <= p < res@.len() && 0 <= q < res@[p].len() ==>
                #[trigger] res@[p][q] == if p > q - k as int { 0.0f32 } else { m@[p][q] },
        decreases (m_len - i) as int
    {
        let mut row: Vec<f32> = Vec::new();
        let row_len = m[i].len();
        let mut j: usize = 0;
        while j < row_len
            invariant
                i < m.len(),
                row_len as int == m@[i as int].len(),
                j <= row_len,
                row@.len() == j as int,
                forall|q: int| 0 <= q < row@.len() ==> #[trigger] row@[q] == if (i as int) > q - k as int { 0.0f32 } else { m@[i as int][q] },
            decreases (row_len - j) as int
        {
            let cond: bool = (i as int) > (j as int) - (k as int);
            let val: f32 = if cond { 0.0f32 } else { m[i][j] };
            row.push(val);
            j += 1;
        }
        res.push(row);
        i += 1;
    }
    res
}
// </vc-code>


}
fn main() {}