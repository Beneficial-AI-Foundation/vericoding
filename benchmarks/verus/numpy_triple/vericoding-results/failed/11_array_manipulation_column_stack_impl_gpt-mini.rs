// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial identity lemma for nat multiplication */
proof fn column_stack_helper(rows: nat, cols: nat) ensures rows * cols == rows * cols { }

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
    /* code modified by LLM (iteration 5): implement column stacking with nested loops and correct invariants */
    let rows: nat = arrays.len();
    let cols: nat = arrays[0].len();
    let mut result: Vec<f32> = Vec::<f32>::new();

    let mut j: nat = 0;
    while j < rows
        invariant j <= rows;
        invariant result.len() == j * cols;
        decreases rows - j
    {
        let mut i: nat = 0;
        while i < cols
            invariant i <= cols;
            invariant result.len() == j * cols + i;
            decreases cols - i
        {
            let val: f32 = arrays[j][i];
            result.push(val);
            i = i + 1;
        }
        j = j + 1;
    }

    result
}
// </vc-code>

}
fn main() {}