// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
spec fn matrix_max_abs(x: Seq<Seq<i8>>) -> int
    decreases x.len()
{
    if x.len() == 0 {
        0
    } else {
        let row_max = seq_max_abs(x[0]);
        let rest_max = matrix_max_abs(x.subrange(1, x.len() as int));
        if row_max > rest_max { row_max } else { rest_max }
    }
}

spec fn seq_max_abs(row: Seq<i8>) -> int
    decreases row.len()
{
    if row.len() == 0 {
        0
    } else if row.len() == 1 {
        abs_val(row[0] as int)
    } else {
        let first_abs = abs_val(row[0] as int);
        let rest_max = seq_max_abs(row.subrange(1, row.len() as int));
        if first_abs > rest_max { first_abs } else { rest_max }
    }
}

/* helper modified by LLM (iteration 5): fixed lemma syntax */
proof fn lemma_matrix_max_abs_bounds(x: Seq<Seq<i8>>)
    requires
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i].len() > 0,
    ensures
        forall|i: int, j: int| 0 <= i < x.len() && 0 <= j < x[i].len() ==> abs_val(x[i][j] as int) <= matrix_max_abs(x),
        (matrix_max_abs(x) == 0) == (forall|i: int, j: int| 0 <= i < x.len() && 0 <= j < x[i].len() ==> x[i][j] == 0)
{
}
// </vc-helpers>

// <vc-spec>
fn matrix_norm(x: Vec<Vec<i8>>) -> (result: i8)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() == x@[0].len(),
    ensures
        result as int >= 0,
        (result as int == 0) == (forall|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() ==> #[trigger] x@[i][j] == 0),
        forall|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() ==> abs_val(#[trigger] x@[i][j] as int) <= result as int,
        (exists|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() && #[trigger] x@[i][j] != 0) ==> result as int > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed int/usize indexing by using int consistently */
    let mut max_val: i8 = 0;
    let mut i = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            max_val as int >= 0,
            forall|row_idx: int, col_idx: int| 0 <= row_idx < i && 0 <= col_idx < x@[row_idx].len() ==> abs_val(x@[row_idx][col_idx] as int) <= max_val as int,
            (max_val == 0) == (forall|row_idx: int, col_idx: int| 0 <= row_idx < i && 0 <= col_idx < x@[row_idx].len() ==> x@[row_idx][col_idx] == 0),
        decreases x.len() - i
    {
        let mut j = 0;
        while j < x[i].len()
            invariant
                0 <= i < x.len(),
                0 <= j <= x@[i as int].len(),
                max_val as int >= 0,
                forall|row_idx: int, col_idx: int| 0 <= row_idx < i && 0 <= col_idx < x@[row_idx].len() ==> abs_val(x@[row_idx][col_idx] as int) <= max_val as int,
                forall|col_idx: int| 0 <= col_idx < j ==> abs_val(x@[i as int][col_idx] as int) <= max_val as int,
            decreases x@[i as int].len() - j
        {
            let abs_current = if x[i][j] >= 0 { x[i][j] } else { -x[i][j] };
            if abs_current > max_val {
                max_val = abs_current;
            }
            j += 1;
        }
        i += 1;
    }
    
    max_val
}
// </vc-code>


}
fn main() {}