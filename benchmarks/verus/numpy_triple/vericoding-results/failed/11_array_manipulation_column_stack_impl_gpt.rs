// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix type mismatches and operate on Seq<Vec<f32>> using views */
spec fn flatten_row_major(arrs: Seq<Vec<f32>>) -> Seq<f32>
    recommends arrs.len() > 0
{
    let rows = arrs.len();
    let cols = arrs.index(0)@.len();
    if cols == 0 {
        Seq::empty()
    } else {
        let cols_i: int = cols as int;
        Seq::new(rows * cols, |k: int| {
            let j = k / cols_i;
            let i = k % cols_i;
            arrs.index(j)@[i]
        })
    }
}
// </vc-helpers>

// <vc-spec>
fn column_stack(arrays: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires
        arrays.len() > 0,
        forall|i: int| 0 <= i < arrays.len() ==> #[trigger] arrays[i].len() == arrays[0].len(),
    ensures
        result.len() == arrays.len() * arrays[0].len(),
        forall|i: int, j: int| 
            0 <= i < arrays[0].len() && 0 <= j < arrays.len() ==>
            #[trigger] result[j * arrays[0].len() + i] == arrays[j][i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement row-major flattening with verified loops */
    let rows = arrays.len();
    let cols = arrays[0].len();
    let mut result: Vec<f32> = Vec::new();
    let mut j: int = 0;
    while j < rows
        invariant
            0 <= j <= rows,
            result.len() == j * cols,
            forall|jj: int, ii: int|
                0 <= jj < j && 0 <= ii < cols ==> result[jj * cols + ii] == arrays[jj][ii]
        decreases rows - j
    {
        let mut i: int = 0;
        while i < cols
            invariant
                0 <= i <= cols,
                result.len() == j * cols + i,
                forall|jj: int, ii: int| 0 <= jj < j && 0 <= ii < cols ==> result[jj * cols + ii] == arrays[jj][ii],
                forall|ii: int| 0 <= ii < i ==> result[j * cols + ii] == arrays[j][ii]
            decreases cols - i
        {
            let old_i = i;
            result.push(arrays[j][i]);
            proof {
                assert(result.len() == j * cols + old_i + 1);
                assert(result@[j * cols + old_i] == arrays[j][old_i]);
            }
            i = i + 1;
        }
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}