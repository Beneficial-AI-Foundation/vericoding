// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): add trigger to uniform row length quantifier */
spec fn all_rows_same_len(m: Seq<Seq<f32>>) -> bool { m.len() == 0 || (forall|i: int| 0 <= i < m.len() ==> #[trigger] m[i].len() == m[0].len()) }
/* helper modified by LLM (iteration 4): commutativity of addition for natural numbers */
proof fn lemma_add_comm_nat(a: nat, b: nat)
    ensures
        a + b == b + a
{ }
// </vc-helpers>

// <vc-spec>
fn block(
    top_left: Vec<Vec<f32>>,
    top_right: Vec<Vec<f32>>,
    bottom_left: Vec<Vec<f32>>,
    bottom_right: Vec<Vec<f32>>
) -> (result: Vec<Vec<f32>>)
    requires
        top_left.len() > 0,
        top_right.len() > 0,
        bottom_left.len() > 0,
        bottom_right.len() > 0,
        top_left.len() == top_right.len(),
        bottom_left.len() == bottom_right.len(),
        top_left[0].len() == bottom_left[0].len(),
        top_right[0].len() == bottom_right[0].len(),
        forall|i: int| 0 <= i < top_left.len() ==> #[trigger] top_left[i].len() == top_left[0].len(),
        forall|i: int| 0 <= i < top_right.len() ==> #[trigger] top_right[i].len() == top_right[0].len(),
        forall|i: int| 0 <= i < bottom_left.len() ==> #[trigger] bottom_left[i].len() == bottom_left[0].len(),
        forall|i: int| 0 <= i < bottom_right.len() ==> #[trigger] bottom_right[i].len() == bottom_right[0].len(),
    ensures
        result.len() == top_left.len() + bottom_left.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == top_left[0].len() + top_right[0].len(),

        forall|i: int, j: int| 
            0 <= i < top_left.len() && 0 <= j < top_left[0].len() ==> 
            #[trigger] result[i][j] == top_left[i][j],

        forall|i: int, j: int|
            0 <= i < top_right.len() && 0 <= j < top_right[0].len() ==>
            #[trigger] result[i][top_left[0].len() + j] == top_right[i][j],

        forall|i: int, j: int|
            0 <= i < bottom_left.len() && 0 <= j < bottom_left[0].len() ==>
            #[trigger] result[top_left.len() + i][j] == bottom_left[i][j],

        forall|i: int, j: int|
            0 <= i < bottom_right.len() && 0 <= j < bottom_right[0].len() ==>
            #[trigger] result[top_left.len() + i][top_left[0].len() + j] == bottom_right[i][j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): add #[trigger] annotations to quantified invariants */
{
    let tl_rows = top_left.len();
    let bl_rows = bottom_left.len();
    let tl_cols = top_left[0].len();
    let tr_cols = top_right[0].len();

    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut i: usize = 0;
    while i < tl_rows
        invariant
            i <= tl_rows,
            result.len() == i,
            forall|r: int| 0 <= r < i as int ==> #[trigger] result[r].len() == tl_cols + tr_cols,
            forall|r: int, c: int| 0 <= r < i as int && 0 <= c < tl_cols as int ==> #[trigger] result[r][c] == top_left[r][c],
            forall|r: int, c: int| 0 <= r < i as int && 0 <= c < tr_cols as int ==> #[trigger] result[r][tl_cols as int + c] == top_right[r][c],
        decreases tl_rows - i
    {
        let mut row: Vec<f32> = Vec::new();

        let mut j: usize = 0;
        while j < tl_cols
            invariant
                j <= tl_cols,
                row.len() == j,
                forall|c: int| 0 <= c < j as int ==> #[trigger] row[c] == top_left[i as int][c],
            decreases tl_cols - j
        {
            row.push(top_left[i][j]);
            j += 1;
        }

        let mut j2: usize = 0;
        while j2 < tr_cols
            invariant
                j2 <= tr_cols,
                row.len() == tl_cols + j2,
                forall|c: int| 0 <= c < tl_cols as int ==> #[trigger] row[c] == top_left[i as int][c],
                forall|c: int| 0 <= c < j2 as int ==> #[trigger] row[tl_cols as int + c] == top_right[i as int][c],
            decreases tr_cols - j2
        {
            row.push(top_right[i][j2]);
            j2 += 1;
        }

        result.push(row);
        i += 1;
    }

    let mut i2: usize = 0;
    while i2 < bl_rows
        invariant
            i2 <= bl_rows,
            result.len() == tl_rows + i2,
            forall|r: int| 0 <= r < tl_rows as int ==> #[trigger] result[r].len() == tl_cols + tr_cols,
            forall|r: int, c: int| 0 <= r < tl_rows as int && 0 <= c < tl_cols as int ==> #[trigger] result[r][c] == top_left[r][c],
            forall|r: int, c: int| 0 <= r < tl_rows as int && 0 <= c < tr_cols as int ==> #[trigger] result[r][tl_cols as int + c] == top_right[r][c],
            forall|r: int| 0 <= r < i2 as int ==> #[trigger] result[tl_rows as int + r].len() == tl_cols + tr_cols,
            forall|r: int, c: int| 0 <= r < i2 as int && 0 <= c < tl_cols as int ==> #[trigger] result[tl_rows as int + r][c] == bottom_left[r][c],
            forall|r: int, c: int| 0 <= r < i2 as int && 0 <= c < tr_cols as int ==> #[trigger] result[tl_rows as int + r][tl_cols as int + c] == bottom_right[r][c],
        decreases bl_rows - i2
    {
        let mut row: Vec<f32> = Vec::new();

        let mut j: usize = 0;
        while j < tl_cols
            invariant
                j <= tl_cols,
                row.len() == j,
                forall|c: int| 0 <= c < j as int ==> #[trigger] row[c] == bottom_left[i2 as int][c],
            decreases tl_cols - j
        {
            row.push(bottom_left[i2][j]);
            j += 1;
        }

        let mut j2: usize = 0;
        while j2 < tr_cols
            invariant
                j2 <= tr_cols,
                row.len() == tl_cols + j2,
                forall|c: int| 0 <= c < tl_cols as int ==> #[trigger] row[c] == bottom_left[i2 as int][c],
                forall|c: int| 0 <= c < j2 as int ==> #[trigger] row[tl_cols as int + c] == bottom_right[i2 as int][c],
            decreases tr_cols - j2
        {
            row.push(bottom_right[i2][j2]);
            j2 += 1;
        }

        result.push(row);
        i2 += 1;
    }

    result
}
// </vc-code>

}
fn main() {}