use vstd::prelude::*;

verus! {

fn column_stack(input: &Vec<Vec<i32>>) -> (ret: Vec<Vec<i32>>)
    requires
        input.len() > 0,
        input@[0].len() > 0,
        forall|i: int| 0 <= i < input.len() ==> #[trigger] input@[i].len() == input@[0].len(),
    ensures
        ret.len() == input@[0].len(),
        forall|i: int| 0 <= i < ret.len() ==> #[trigger] ret@[i].len() == input.len(),
        forall|i: int, j: int| 
            0 <= i < input.len() && 0 <= j < input@[0].len() ==> 
            #[trigger] ret@[j]@[i] == #[trigger] input@[i]@[j],
{
    let input_rows = input.len();
    let input_cols = input[0].len();
    
    let mut ret: Vec<Vec<i32>> = Vec::new();
    let mut j: usize = 0;
    
    while j < input_cols
        invariant
            input_rows > 0,
            input_cols > 0,
            input_rows == input.len(),
            input_cols == input@[0].len(),
            0 <= j <= input_cols,
            ret.len() == j,
            forall|col: int| 0 <= col < j ==> #[trigger] ret@[col].len() == input_rows,
            forall|i: int, col: int| 
                0 <= i < input_rows && 0 <= col < j ==> 
                #[trigger] ret@[col]@[i] == #[trigger] input@[i]@[col],
            forall|i: int| 0 <= i < input.len() ==> #[trigger] input@[i].len() == input_cols,
        decreases input_cols - j,
    {
        let mut column: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        
        while i < input_rows
            invariant
                0 <= i <= input_rows,
                0 <= j < input_cols,
                input_rows == input.len(),
                input_cols == input@[0].len(),
                column.len() == i,
                forall|row: int| 0 <= row < i ==> #[trigger] column@[row] == #[trigger] input@[row]@[j as int],
                forall|k: int| 0 <= k < input.len() ==> #[trigger] input@[k].len() == input_cols,
            decreases input_rows - i,
        {
            assert(i < input.len());
            assert(j < input@[i as int].len()) by {
                assert(input@[i as int].len() == input_cols);
                assert(j < input_cols);
            };
            column.push(input[i][j]);
            i += 1;
        }
        
        ret.push(column);
        j += 1;
    }
    
    ret
}

fn main() {}

}