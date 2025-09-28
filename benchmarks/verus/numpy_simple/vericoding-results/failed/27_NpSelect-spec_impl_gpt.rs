// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove row length equality via the provided universal equality */
proof fn row_len_eq_from_all(condlist: &Vec<Vec<bool>>, i: int)
    requires
        0 <= i < condlist@.len(),
        forall|a: int, b: int| 0 <= a < condlist@.len() && 0 <= b < condlist@.len() ==> condlist@[a].len() == condlist@[b].len(),
    ensures
        condlist@[i].len() == condlist@[0].len(),
{
    assert(condlist@.len() > 0);
    assert(condlist@[i].len() == condlist@[0].len());
}

/* helper modified by LLM (iteration 2): from j in first row and all rows equal length, j is in range for all rows */
proof fn col_in_range_all_rows(condlist: &Vec<Vec<bool>>, j: int)
    requires
        condlist@.len() > 0,
        0 <= j < condlist@[0].len(),
        forall|a: int, b: int| 0 <= a < condlist@.len() && 0 <= b < condlist@.len() ==> condlist@[a].len() == condlist@[b].len(),
    ensures
        forall|i: int| 0 <= i < condlist@.len() ==> 0 <= j < condlist@[i].len(),
{
    assert_forall_by(|i: int| {
        requires
            0 <= i < condlist@.len(),
        ensures
            0 <= j < condlist@[i].len(),
        {
            assert(condlist@[i].len() == condlist@[0].len());
            assert(0 <= j < condlist@[0].len());
        }
    });
}

// </vc-helpers>

// <vc-spec>
fn select(condlist: Vec<Vec<bool>>, choicelist: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        condlist@.len() > 0,
        condlist@.len() == choicelist@.len(),
        forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() > 0,
        forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() == choicelist@[i].len(),
        forall|i: int, j: int| 0 <= i < condlist@.len() && 0 <= j < condlist@.len() ==> 
            condlist@[i].len() == condlist@[j].len(),
    ensures
        result@.len() == condlist@[0].len(),
        forall|i: int, j: int| 
            0 <= i < condlist@.len() && 0 <= j < result@.len() && condlist@[i][j] ==> 
            result@[j] == choicelist@[i][j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix usize/int mismatch in assertions and maintain safe indexing */
    let nrows: usize = condlist.len();
    let ncols: usize = condlist[0].len();

    let mut result: Vec<f32> = Vec::new();

    // initialize result with zeros to required length
    let mut j: usize = 0;
    while j < ncols
        invariant
            j <= ncols,
            result.len() == j,
        decreases (ncols - j) as int
    {
        result.push(0.0f32);
        j = j + 1;
    }

    let mut col: usize = 0;
    while col < ncols
        invariant
            col <= ncols,
            result.len() == ncols,
        decreases (ncols - col) as int
    {
        let mut val: f32 = result[col];
        let mut i: usize = 0;
        while i < nrows
            invariant
                i <= nrows,
                col < ncols,
                result.len() == ncols,
            decreases (nrows - i) as int
        {
            // Safe indexing obligations (cast to int for spec assertion types)
            assert((col as int) < (condlist[i].len() as int));
            assert((col as int) < (choicelist[i].len() as int));
            if condlist[i][col] {
                val = choicelist[i][col];
            }
            i = i + 1;
        }
        result[col] = val;
        col = col + 1;
    }

    result
}
// </vc-code>


}
fn main() {}