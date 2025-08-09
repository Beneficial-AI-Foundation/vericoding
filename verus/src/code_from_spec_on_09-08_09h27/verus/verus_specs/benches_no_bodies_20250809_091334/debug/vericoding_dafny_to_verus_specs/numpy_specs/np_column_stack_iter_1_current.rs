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
    
    let mut col_idx: usize = 0;
    while col_idx < num_cols
        invariant
            col_idx <= num_cols,
            result@.len() == col_idx,
            forall|j: int| 0 <= j < result@.len() ==> #[trigger] result@[j].len() == input@.len(),
            forall|i: int, j: int| 
                0 <= i < input@.len() && 0 <= j < col_idx ==> 
                result@[j]@[i] == input@[i]@[j],
    {
        let mut column: Vec<i32> = Vec::new();
        let mut row_idx: usize = 0;
        
        while row_idx < num_rows
            invariant
                row_idx <= num_rows,
                column@.len() == row_idx,
                col_idx < num_cols,
                forall|i: int| 0 <= i < row_idx ==> column@[i] == input@[i]@[col_idx as int],
        {
            column.push(input[row_idx][col_idx]);
            row_idx += 1;
        }
        
        result.push(column);
        col_idx += 1;
    }
    
    result
}

fn main() {}

}