// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn triu(m: &Vec<Vec<f32>>, k: i8) -> (result: Vec<Vec<f32>>)
    requires 
        m@.len() > 0,
        forall|i: int| 0 <= i < m@.len() ==> #[trigger] m@[i].len() == m@[0].len(),
    ensures
        result@.len() == m@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i].len() == m@[i].len(),
        forall|i: int, j: int| 
            0 <= i < result@.len() && 0 <= j < result@[i].len() ==>
            #[trigger] result@[i][j] == if i > j - k as int { 0.0f32 } else { m@[i][j] },
        forall|i: int, j: int|
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i <= j - k as int ==>
            #[trigger] result@[i][j] == m@[i][j],
        forall|i: int, j: int|
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i > j - k as int ==>
            #[trigger] result@[i][j] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix invariant and arithmetic operations */
    let mut result: Vec<Vec<f32>> = Vec::new();
    
    let mut i = 0;
    while i < m.len()
        invariant
            i <= m@.len(),
            result@.len() == i,
            forall|idx: int| 0 <= idx < i ==> #[trigger] result@[idx].len() == m@[idx].len(),
            forall|row: int, col: int| 
                0 <= row < i && 0 <= col < result@[row].len() ==> 
                #[trigger] result@[row][col] == if row > col - k as int { 0.0f32 } else { m@[row][col] },
        decreases m@.len() - i
    {
        let mut new_row: Vec<f32> = Vec::new();
        
        let mut j = 0;
        while j < m[i].len()
            invariant
                i < m@.len(),
                j <= m@[i as int].len(),
                new_row@.len() == j,
                forall|col: int| 
                    0 <= col < j ==> 
                    #[trigger] new_row@[col] == if i as int > col - k as int { 0.0f32 } else { m@[i as int][col] },
            decreases m@[i as int].len() - j
        {
            if i as int > j as int - k as int {
                new_row.push(0.0f32);
            } else {
                new_row.push(m[i][j]);
            }
            
            proof {
                assert(new_row@.len() == j + 1);
                assert(forall|col: int| 
                    0 <= col < j ==> 
                    new_row@[col] == if i as int > col - k as int { 0.0f32 } else { m@[i as int][col] });
                assert(new_row@[j as int] == if i as int > j as int - k as int { 0.0f32 } else { m@[i as int][j as int] });
            }
            
            j += 1;
        }
        
        result.push(new_row);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}