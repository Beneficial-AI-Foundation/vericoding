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
/* helper modified by LLM (iteration 5): linear_index helper for 2D to 1D index used as trigger */
pub open spec fn linear_index(i: int, j: int, cols: int) -> int { i * cols + j }
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
    /* code modified by LLM (iteration 5): implement flatten using int indices and explicit invariants/proofs */
    let mut ret: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < (mat.rows as int)
        invariant
            (ret.len() as int) == i * (mat.cols as int),
            forall|ii: int, jj: int|
                0 <= ii < i && 0 <= jj < (mat.cols as int) ==> (ret@[(#[trigger] linear_index(ii, jj, mat.cols as int)) as int] == mat.get(ii as usize, jj as usize)),
        decreases (mat.rows as int) - i
    {
        let mut j: int = 0;
        while j < (mat.cols as int)
            invariant
                (ret.len() as int) == i * (mat.cols as int) + j,
                forall|ii: int, jj: int|
                    ((0 <= ii < i && 0 <= jj < (mat.cols as int)) || (ii == i && 0 <= jj < j)) ==> (ret@[(#[trigger] linear_index(ii, jj, mat.cols as int)) as int] == mat.get(ii as usize, jj as usize)),
            decreases (mat.cols as int) - j
        {
            proof {
                // establish bounds needed to index mat.data and push
                assert(mat.valid());
                assert(0 <= i && i < (mat.rows as int));
                assert(0 <= j && j < (mat.cols as int));
                // from mat.valid and 0 <= i < rows we get mat.data[i].len() == mat.cols
                assert(mat.data[i].len() == mat.cols);
            }
            ret.push(mat.data[i][j]);
            j = j + 1;
        }
        i = i + 1;
    }
    ret
}
// </vc-code>


}
fn main() {}