use vstd::prelude::*;

verus! {

fn ravel<T: Copy>(arr: &Vec<Vec<T>>) -> (ret: Vec<T>)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr[0].len(),
    ensures
        ret.len() == arr.len() * arr[0].len(),
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
            ret[i * arr[0].len() + j] == arr[i][j],
{
    let rows = arr.len();
    let cols = arr[0].len();
    let mut ret: Vec<T> = Vec::new();
    
    let mut row: usize = 0;
    while row < rows
        invariant
            row <= rows,
            ret.len() == row * cols,
            forall|i: int, j: int| 0 <= i < row && 0 <= j < cols ==> 
                ret[i * cols + j] == arr[i][j],
        decreases rows - row,
    {
        let mut col: usize = 0;
        while col < cols
            invariant
                col <= cols,
                ret.len() == row * cols + col,
                forall|i: int, j: int| 0 <= i < row && 0 <= j < cols ==> 
                    ret[i * cols + j] == arr[i][j],
                forall|j: int| 0 <= j < col ==> 
                    ret[(row as int) * (cols as int) + j] == arr[row as int][j],
            decreases cols - col,
        {
            ret.push(arr[row][col]);
            col += 1;
        }
        row += 1;
    }
    ret
}

}

fn main() {}