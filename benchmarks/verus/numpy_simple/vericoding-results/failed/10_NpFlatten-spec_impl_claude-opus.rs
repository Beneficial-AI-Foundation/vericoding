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
    /* code modified by LLM (iteration 5): Fixed bounds checks and invariant maintenance */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < mat.rows
        invariant
            mat.rows > 0,
            mat.cols > 0,
            mat.valid(),
            0 <= i <= mat.rows,
            result.len() == i * mat.cols,
            forall|row: int, col: int| 
                0 <= row < i && 0 <= col < mat.cols ==> 
                row * (mat.cols as int) + col < result.len() &&
                result@[row * (mat.cols as int) + col] == mat.get(row as usize, col as usize),
        decreases mat.rows - i
    {
        let mut j: usize = 0;
        while j < mat.cols
            invariant
                mat.rows > 0,
                mat.cols > 0,
                mat.valid(),
                0 <= i < mat.rows,
                0 <= j <= mat.cols,
                result.len() == i * mat.cols + j,
                forall|row: int, col: int| 
                    0 <= row < i && 0 <= col < mat.cols ==> 
                    row * (mat.cols as int) + col < result.len() &&
                    result@[row * (mat.cols as int) + col] == mat.get(row as usize, col as usize),
                forall|col: int|
                    0 <= col < j ==> 
                    i * (mat.cols as int) + col < result.len() &&
                    result@[i * (mat.cols as int) + col] == mat.get(i, col as usize),
            decreases mat.cols - j
        {
            result.push(mat.data[i][j]);
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}