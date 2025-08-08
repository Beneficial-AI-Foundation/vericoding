use vstd::prelude::*;

verus! {

fn ravel<T: Copy>(arr: &Vec<Vec<T>>) -> (ret: Vec<T>)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr[0].len(),
    ensures
        ret.len() == arr.len() * arr[0].len(),
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr[0].len()
            ==> ret[i * arr[0].len() + j] == arr[i][j],
{
    let mut ret_vec: Vec<T> = Vec::new();
    let rows = arr.len();
    let cols = arr[0].len();
    
    let mut row = 0;
    while row < rows
        invariant
            0 <= row <= rows,
            ret_vec.len() == row * cols,
            forall|i: int, j: int| 0 <= i < row && 0 <= j < cols 
                ==> ret_vec[i * cols + j] == arr[i][j],
        decreases rows - row
    {
        let mut col = 0;
        while col < cols
            invariant
                0 <= col <= cols,
                0 <= row < rows,
                ret_vec.len() == row * cols + col,
                forall|i: int, j: int| 0 <= i < row && 0 <= j < cols 
                    ==> ret_vec[i * cols + j] == arr[i][j],
                forall|j: int| 0 <= j < col 
                    ==> ret_vec[row * cols + j] == arr[row as int][j],
            decreases cols - col
        {
            ret_vec.push(arr[row][col]);
            col = col + 1;
        }
        row = row + 1;
    }
    
    ret_vec
}

fn main() {}

}