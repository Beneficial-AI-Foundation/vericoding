// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Matrix type definition - 2D array represented as vector of vectors */
pub struct Matrix {
    pub data: Vec<Vec<i32>>,
    pub rows: usize,
    pub cols: usize,
}

impl Matrix {
    pub open spec fn size(&self) -> nat {
        (self.rows * self.cols) as nat
    }

    pub open spec fn valid(&self) -> bool {
        &&& self.data.len() == self.rows
        &&& forall|i: int| 0 <= i < self.rows ==> self.data[i].len() == self.cols
    }

    pub open spec fn get(&self, i: usize, j: usize) -> i32 
        recommends self.valid() && i < self.rows && j < self.cols
    {
        self.data[i as int][j as int]
    }
}
// </vc-preamble>

// <vc-helpers>
fn flatten2_helper(mat: &Matrix, row: usize, col: usize, index: usize, output: &mut Vec<i32>)
    requires
        mat.rows > 0,
        mat.cols > 0,
        mat.valid(),
        row < mat.rows,
        col < mat.cols,
        index == (row as int) * (mat.cols as int) + (col as int),
        output.len() == index,
    ensures
        output.len() == index + 1,
        output@[index as int] == mat.get(row, col),
{
    output.push(mat.data[row][col]);
}
// </vc-helpers>

// <vc-spec>
fn flatten2(mat: &Matrix) -> (ret: Vec<i32>)
    requires 
        mat.rows > 0,
        mat.cols > 0,
        mat.valid(),
    ensures
        ret.len() == mat.rows * mat.cols,
        forall|i: int, j: int| 
            0 <= i < mat.rows && 0 <= j < mat.cols ==> 
            #[trigger] ret@[(i * (mat.cols as int) + j) as int] == mat.get(i as usize, j as usize),
// </vc-spec>
// <vc-code>
{
    let mut output: Vec<i32> = Vec::new();
    let mut row = 0;
    
    while row < mat.rows
        invariant
            0 <= row <= mat.rows,
            output.len() == (row as int) * (mat.cols as int),
            forall|i: int, j: int|
                0 <= i < row && 0 <= j < mat.cols ==>
                #[trigger] output@[(i * (mat.cols as int) + j) as int] == mat.get(i as usize, j as usize),
        decreases mat.rows - row
    {
        let mut col = 0;
        while col < mat.cols
            invariant
                0 <= col <= mat.cols,
                output.len() == (row as int) * (mat.cols as int) + (col as int),
                forall|i: int, j: int|
                    0 <= i < row && 0 <= j < mat.cols ==>
                    #[trigger] output@[(i * (mat.cols as int) + j) as int] == mat.get(i as usize, j as usize),
                forall|j: int|
                    0 <= j < col ==>
                    #[trigger] output@[((row as int) * (mat.cols as int) + j) as int] == mat.get(row, j as usize),
            decreases mat.cols - col
        {
            let index = (row as int) * (mat.cols as int) + (col as int);
            output.push(mat.data[row][col]);
            col += 1;
        }
        row += 1;
    }
    output
}
// </vc-code>


}
fn main() {}