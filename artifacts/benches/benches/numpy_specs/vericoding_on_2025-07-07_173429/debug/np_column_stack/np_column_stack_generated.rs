use vstd::prelude::*;

verus! {

fn column_stack(input: &Vec<Vec<i32>>) -> (ret: Vec<Vec<i32>>)
    requires
        input.len() > 0,
        forall|i: int| 0 <= i < input.len() ==> #[trigger] input@[i].len() == input@[0].len(),
    ensures
        ret.len() == input@[0].len(),
        forall|i: int| 0 <= i < ret.len() ==> #[trigger] ret@[i].len() == input.len(),
        forall|i: int, j: int| 
            0 <= i < input.len() && 0 <= j < input@[0].len() ==> 
            #[trigger] ret@[j]@[i] == input@[i]@[j],
{
    let input_rows = input.len();
    let input_cols = input[0].len();
    let mut ret: Vec<Vec<i32>> = Vec::new();
    
    // Initialize the result matrix with the transposed dimensions
    let mut col = 0;
    while col < input_cols
        invariant
            0 <= col <= input_cols,
            input_rows == input.len(),
            input_cols == input@[0].len(),
            ret.len() == col,
            forall|k: int| 0 <= k < col ==> #[trigger] ret@[k].len() == input_rows,
            forall|i: int, j: int| 
                0 <= i < input_rows && 0 <= j < col ==> 
                #[trigger] ret@[j]@[i] == input@[i]@[j],
            forall|i: int| 0 <= i < input.len() ==> input@[i].len() == input_cols,
        decreases input_cols - col,
    {
        let mut row_vec: Vec<i32> = Vec::new();
        let mut row = 0;
        while row < input_rows
            invariant
                0 <= row <= input_rows,
                0 <= col < input_cols,
                input_rows == input.len(),
                input_cols == input@[0].len(),
                row_vec.len() == row,
                forall|r: int| 0 <= r < row ==> #[trigger] row_vec@[r] == input@[r]@[col as int],
                forall|i: int| 0 <= i < input.len() ==> input@[i].len() == input_cols,
            decreases input_rows - row,
        {
            assert(row < input.len());
            assert(col < input@[row as int].len());
            row_vec.push(input[row][col]);
            row += 1;
        }
        ret.push(row_vec);
        col += 1;
    }
    
    ret
}

fn main() {}

}