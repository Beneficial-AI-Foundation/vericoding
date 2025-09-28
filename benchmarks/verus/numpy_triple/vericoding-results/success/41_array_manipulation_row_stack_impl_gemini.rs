// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn row_stack(arrays: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires arrays.len() > 0,
             forall|i: int| 0 <= i < arrays.len() ==> arrays[i].len() > 0,
             forall|i: int, j: int| 0 <= i < arrays.len() && 0 <= j < arrays.len() ==> 
                 arrays[i].len() == arrays[j].len(),
    ensures result.len() == arrays.len(),
            forall|i: int| 0 <= i < result.len() ==> result[i].len() == arrays[i].len(),
            forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==>
                result[i][j] == arrays[i][j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error by replacing `new_with_capacity` with `with_capacity`. */
    let mut result: Vec<Vec<f32>> = Vec::with_capacity(arrays.len());
    let mut i: usize = 0;
    while i < arrays.len()
        invariant
            0 <= i <= arrays.len(),
            result.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> result@[k].view() == arrays@[k].view(),
        decreases arrays.len() - i
    {
        let row = &arrays[i];
        let mut new_row: Vec<f32> = Vec::with_capacity(row.len());
        let mut j: usize = 0;

        while j < row.len()
            invariant
                0 <= j <= row.len(),
                new_row.len() == j as int,
                forall|k: int| 0 <= k < j as int ==> new_row@[k] == row@[k],
            decreases row.len() - j
        {
            new_row.push(row[j]);
            j = j + 1;
        }

        assert(new_row.view() == row.view());
        result.push(new_row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}