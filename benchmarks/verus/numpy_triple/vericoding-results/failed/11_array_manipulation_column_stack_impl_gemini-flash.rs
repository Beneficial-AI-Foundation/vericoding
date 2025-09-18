// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Corrected loop bounds and invariants to match the column-major ordering. Modified indexing to `result@[c * num_rows + r]` to correctly represent column stacking. */
{
    let num_rows = arrays.len() as int;
    let num_cols = arrays[0].len() as int;
    let mut result: Vec<f32> = Vec::with_capacity(num_rows * num_cols);

    for i in 0..num_cols
        invariant
            result.len() == i * num_rows,
            forall|r: int, c: int|
                0 <= r < num_rows && 0 <= c < i ==> 
                #[trigger] result@[(c * num_rows + r) as int] == arrays@[r as int][c as int],
    {
        for j in 0..num_rows
            invariant
                result.len() == i * num_rows + j,
                forall|r: int, c: int|
                    0 <= c < i ==> 
                        forall|idx: int|
                            0 <= idx < num_rows ==> 
                                #[trigger] result@[(c * num_rows + idx) as int] == arrays@[idx as int][c as int],
                forall|r_inner: int|
                    0 <= r_inner < j ==> 
                        #[trigger] result@[(i * num_rows + r_inner) as int] == arrays@[r_inner as int][i as int],
            requires(
                (num_rows as usize) < arrays.len() && (i as usize) < arrays[0].len()
            )
        {
            result.push(arrays[j as usize][i as usize]);
        }
    }

    result
}
// </vc-code>

}
fn main() {}