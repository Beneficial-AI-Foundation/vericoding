use vstd::prelude::*;

verus! {

// Specification-only function declaration (like a method signature in Dafny)
fn column_stack(input: &Vec<Vec<i32>>) -> (ret: Vec<Vec<i32>>)
    requires 
        input.len() != 0,
        forall|i: int| 0 <= i < input.len() ==> #[trigger] input@[i].len() == input@[0].len(),
    ensures 
        ret@.len() == input@[0].len(),
        forall|j: int| 0 <= j < ret@.len() ==> #[trigger] ret@[j].len() == input@.len(),
        forall|i: int, j: int| 
            0 <= i < input@.len() && 0 <= j < input@[0].len() ==> 
            ret@[j]@[i] == input@[i]@[j],
{
    let mut result: Vec<Vec<i32>> = Vec::new();
    let num_cols = input[0].len();
    let num_rows = input.len();
    
    for col in 0..num_cols
        invariant
            result@.len() == col,
            forall|j: int| 0 <= j < result@.len() ==> #[trigger] result@[j].len() == input@.len(),
            forall|i: int, j: int| 
                0 <= i < input@.len() && 0 <= j < col ==> 
                result@[j]@[i] == input@[i]@[j],
    {
        let mut new_row: Vec<i32> = Vec::new();
        
        for row in 0..num_rows
            invariant
                new_row@.len() == row,
                /* code modified by LLM (iteration 1): fixed type mismatch by casting col to int */
                forall|i: int| 0 <= i < row ==> new_row@[i] == input@[i]@[col as int],
        {
            new_row.push(input[row][col]);
        }
        
        result.push(new_row);
    }
    
    result
}

fn main() {}

}