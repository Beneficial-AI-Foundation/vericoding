// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_dstack(arrays: Vec<Vec<f32>>) -> (result: Vec<Vec<Vec<f32>>>)
    requires 
        arrays.len() > 0,
        forall|i: int| #![trigger arrays[i]] 0 <= i < arrays.len() ==> 
            forall|j: int| 0 <= j < arrays.len() ==> arrays[i].len() == arrays[j].len(),
    ensures
        result.len() == 1,
        result[0].len() == if arrays.len() > 0 { arrays[0].len() } else { 0 },
        forall|i: int| #![trigger result[0][i]] 0 <= i < result[0].len() ==> result[0][i].len() == arrays.len(),
        forall|i: int, j: int| #![trigger result[0][i][j]]
            0 <= i < result[0].len() && 0 <= j < arrays.len() ==>
            result[0][i][j] == arrays[j][i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed a compilation error in a proof block by using Verus-specific syntax for sequences. */
    let num_rows = arrays[0].len();
    let mut stacked_array: Vec<Vec<f32>> = Vec::new();

    let mut i: usize = 0;
    while i < num_rows
        invariant
            0 <= i <= num_rows,
            arrays.len() > 0,
            forall|k: int| 0 <= k < (arrays.len() as int) ==> arrays@[k].view().len() == (num_rows as int),
            stacked_array.view().len() == (i as int),
            forall|k: int| 0 <= k < (i as int) ==> stacked_array@[k].view().len() == (arrays.len() as int),
            forall|k: int, l: int| 0 <= k < (i as int) && 0 <= l < (arrays.len() as int) ==> stacked_array@[k]@[l] == arrays@[l]@[k]
        decreases num_rows - i
    {
        let mut new_row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < arrays.len()
            invariant
                0 <= j <= arrays.len(),
                i < num_rows,
                arrays.len() > 0,
                forall|k: int| 0 <= k < (arrays.len() as int) ==> arrays@[k].view().len() == (num_rows as int),
                new_row.view().len() == (j as int),
                forall|l: int| 0 <= l < (j as int) ==> new_row@[l] == arrays@[l]@[i as int]
            decreases arrays.len() - j
        {
            proof {
                assert((i as int) < arrays@[j as int].view().len());
            }
            new_row.push(arrays[j][i]);
            j = j + 1;
        }
        stacked_array.push(new_row);
        i = i + 1;
    }

    let result = vec![stacked_array];
    result
}
// </vc-code>

}
fn main() {}