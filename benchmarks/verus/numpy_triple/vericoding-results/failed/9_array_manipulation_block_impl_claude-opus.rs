// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 3): Added decreases clauses to all while loops */
    let mut result: Vec<Vec<f32>> = Vec::new();
    
    // Build top rows (top_left + top_right)
    let mut i: usize = 0;
    while i < top_left.len()
        invariant
            i <= top_left.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == top_left[0].len() + top_right[0].len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < top_left[0].len() ==> #[trigger] result[k][j] == top_left[k][j],
            forall|k: int, j: int| 0 <= k < i && 0 <= j < top_right[0].len() ==> #[trigger] result[k][top_left[0].len() + j] == top_right[k][j],
        decreases top_left.len() - i
    {
        let mut row: Vec<f32> = Vec::new();
        
        // Add elements from top_left[i]
        let mut j: usize = 0;
        while j < top_left[i].len()
            invariant
                j <= top_left[i as int].len(),
                row.len() == j,
                forall|k: int| 0 <= k < j ==> #[trigger] row[k] == top_left[i as int][k],
            decreases top_left[i as int].len() - j
        {
            row.push(top_left[i][j]);
            j = j + 1;
        }
        
        // Add elements from top_right[i]
        let mut j: usize = 0;
        while j < top_right[i].len()
            invariant
                j <= top_right[i as int].len(),
                row.len() == top_left[i as int].len() + j,
                forall|k: int| 0 <= k < top_left[i as int].len() ==> #[trigger] row[k] == top_left[i as int][k],
                forall|k: int| 0 <= k < j ==> #[trigger] row[top_left[i as int].len() + k] == top_right[i as int][k],
            decreases top_right[i as int].len() - j
        {
            row.push(top_right[i][j]);
            j = j + 1;
        }
        
        result.push(row);
        i = i + 1;
    }
    
    // Build bottom rows (bottom_left + bottom_right)
    let mut i: usize = 0;
    while i < bottom_left.len()
        invariant
            i <= bottom_left.len(),
            result.len() == top_left.len() + i,
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == top_left[0].len() + top_right[0].len(),
            forall|k: int, j: int| 0 <= k < top_left.len() && 0 <= j < top_left[0].len() ==> #[trigger] result[k][j] == top_left[k][j],
            forall|k: int, j: int| 0 <= k < top_right.len() && 0 <= j < top_right[0].len() ==> #[trigger] result[k][top_left[0].len() + j] == top_right[k][j],
            forall|k: int, j: int| 0 <= k < i && 0 <= j < bottom_left[0].len() ==> #[trigger] result[top_left.len() + k][j] == bottom_left[k][j],
            forall|k: int, j: int| 0 <= k < i && 0 <= j < bottom_right[0].len() ==> #[trigger] result[top_left.len() + k][top_left[0].len() + j] == bottom_right[k][j],
        decreases bottom_left.len() - i
    {
        let mut row: Vec<f32> = Vec::new();
        
        // Add elements from bottom_left[i]
        let mut j: usize = 0;
        while j < bottom_left[i].len()
            invariant
                j <= bottom_left[i as int].len(),
                row.len() == j,
                forall|k: int| 0 <= k < j ==> #[trigger] row[k] == bottom_left[i as int][k],
            decreases bottom_left[i as int].len() - j
        {
            row.push(bottom_left[i][j]);
            j = j + 1;
        }
        
        // Add elements from bottom_right[i]
        let mut j: usize = 0;
        while j < bottom_right[i].len()
            invariant
                j <= bottom_right[i as int].len(),
                row.len() == bottom_left[i as int].len() + j,
                forall|k: int| 0 <= k < bottom_left[i as int].len() ==> #[trigger] row[k] == bottom_left[i as int][k],
                forall|k: int| 0 <= k < j ==> #[trigger] row[bottom_left[i as int].len() + k] == bottom_right[i as int][k],
            decreases bottom_right[i as int].len() - j
        {
            row.push(bottom_right[i][j]);
            j = j + 1;
        }
        
        result.push(row);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}