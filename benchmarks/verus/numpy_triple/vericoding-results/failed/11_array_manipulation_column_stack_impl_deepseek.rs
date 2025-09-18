// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed requires/ensures from spec function */
spec fn arrays_equal_length(arrays: Vec<Vec<f32>>) -> bool {
    arrays.len() > 0 && (
        forall|i: int| 0 <= i < arrays.len() ==> #[trigger] arrays[i].len() == arrays[0].len()
    )
}

proof fn index_calculation_lemma(i: int, j: int, row_len: int, arrays_len: int) 
    ensures 
        row_len == arrays_len ==> j * row_len + i == i * arrays_len + j,
        0 <= i < row_len && 0 <= j < arrays_len ==> j * row_len + i < arrays_len * row_len
{
}

spec fn get_element(arrays: Vec<Vec<f32>>, i: int, j: int) -> f32 
{
    arrays[j][i]
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
/* code modified by LLM (iteration 5): Fixed compilation error by removing requires from spec function */
{
    let row_len = arrays[0].len();
    let col_len = arrays.len();
    let total_len = col_len * row_len;
    
    let mut result = Vec::new();
    result.resize(total_len, 0.0f32);
    
    let mut j = 0;
    while j < col_len
        invariant
            0 <= j <= col_len,
            result.len() == total_len,
            forall|k: int| 0 <= k < j * row_len ==> #[trigger] result[k] == get_element(arrays, (k as int) % row_len as int, (k as int) / row_len as int),
            forall|k: int| j * row_len <= k < total_len ==> result[k] == 0.0f32
        decreases col_len - j
    {
        let mut i = 0;
        while i < row_len
            invariant
                0 <= i <= row_len,
                result.len() == total_len,
                forall|k: int| 0 <= k < j * row_len + i ==> #[trigger] result[k] == get_element(arrays, (k as int) % row_len as int, (k as int) / row_len as int),
                forall|k: int| j * row_len + i <= k < total_len ==> result[k] == 0.0f32
            decreases row_len - i
        {
            let index = j * row_len + i;
            result[index] = arrays[j][i];
            i += 1;
        }
        j += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}