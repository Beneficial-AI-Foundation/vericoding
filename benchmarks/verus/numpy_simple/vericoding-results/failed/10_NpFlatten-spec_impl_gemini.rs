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
    /* code modified by LLM (iteration 5): used nat arithmetic for vector length invariants */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < mat.rows
        invariant
            mat.rows > 0,
            mat.cols > 0,
            mat.valid(),
            0 <= i <= mat.rows,
            result@.len() == (i as nat) * (mat.cols as nat),
            forall|r: int, c: int|
                0 <= r < i as int && 0 <= c < mat.cols as int ==>
                #[trigger] result@[(r * (mat.cols as int) + c) as int] == mat.get(r as usize, c as usize),
        decreases mat.rows - i
    {
        let mut j: usize = 0;
        while j < mat.cols
            invariant
                mat.rows > 0,
                mat.cols > 0,
                mat.valid(),
                i < mat.rows,
                0 <= j <= mat.cols,
                result@.len() == (i as nat) * (mat.cols as nat) + (j as nat),
                forall|r: int, c: int|
                    0 <= r < i as int && 0 <= c < mat.cols as int ==>
                    #[trigger] result@[(r * (mat.cols as int) + c) as int] == mat.get(r as usize, c as usize),
                forall|c: int|
                    0 <= c < j as int ==>
                    #[trigger] result@[(i as int * (mat.cols as int) + c) as int] == mat.get(i, c as usize),
            decreases mat.cols - j
        {
            let elem = mat.data[i][j];
            result.push(elem);
            j = j + 1;
        }
        i = i + 1;
    }

    result
}

// </vc-code>


}
fn main() {}