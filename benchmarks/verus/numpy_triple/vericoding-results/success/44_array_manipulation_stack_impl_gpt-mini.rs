// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add trigger annotations for inner lengths */
spec fn inner_len_equal(arrays: Vec<Vec<f32>>) -> bool { forall|i: int| 0 <= i < arrays.len() ==> #[trigger] arrays[i].len() == #[trigger] arrays[0].len() }
// </vc-helpers>

// <vc-spec>
fn stack(arrays: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        arrays.len() > 0,
        forall|i: int| 0 <= i < arrays.len() ==> #[trigger] arrays[i].len() == arrays[0].len(),
    ensures
        result.len() == arrays.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == arrays[0].len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> #[trigger] result[i][j] == #[trigger] arrays[i][j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): return the input arrays as the stacked result */
    arrays
}
// </vc-code>

}
fn main() {}