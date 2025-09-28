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
/* helper modified by LLM (iteration 5): simplified lemma to prove basic arithmetic properties */
proof fn lemma_flatten_index_bounds(i: int, j: int, rows: usize, cols: usize)
    requires
        0 <= i < rows,
        0 <= j < cols,
        rows > 0,
        cols > 0,
    ensures
        0 <= i * (cols as int) + j < (rows * cols) as int,
{
    /* Basic bounds checking */
    assert(0 <= j < cols as int);
    assert(0 <= i < rows as int);
    
    /* Lower bound */
    assert(i >= 0 && cols > 0);
    assert(i * (cols as int) >= 0);
    assert(i * (cols as int) + j >= j >= 0);
    
    /* Upper bound */
    assert(i < rows as int);
    assert(j < cols as int);
    assert(i * (cols as int) + j < i * (cols as int) + (cols as int));
    
    /* Prove arithmetic identity step by step */
    assert(i * (cols as int) + (cols as int) == (i + 1) * (cols as int));
    
    /* Since i < rows, we have i + 1 <= rows */
    assert(i + 1 <= rows as int);
    assert((i + 1) * (cols as int) <= (rows as int) * (cols as int));
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
    /* code modified by LLM (iteration 5): fixed bounds checking and invariants */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < mat.rows
        invariant
            i <= mat.rows,
            result.len() == i * mat.cols,
            mat.valid(),
            forall|ii: int, jj: int|
                0 <= ii < i && 0 <= jj < mat.cols ==> {
                    &&& 0 <= ii * (mat.cols as int) + jj < result.len() as int
                    &&& result@[(ii * (mat.cols as int) + jj) as int] == mat.get(ii as usize, jj as usize)
                },
        decreases mat.rows - i
    {
        let mut j = 0;
        
        while j < mat.cols
            invariant
                i < mat.rows,
                j <= mat.cols,
                mat.valid(),
                result.len() == i * mat.cols + j,
                forall|ii: int, jj: int|
                    0 <= ii < i && 0 <= jj < mat.cols ==> {
                        &&& 0 <= ii * (mat.cols as int) + jj < result.len() as int
                        &&& result@[(ii * (mat.cols as int) + jj) as int] == mat.get(ii as usize, jj as usize)
                    },
                forall|jj: int|
                    0 <= jj < j ==> {
                        &&& 0 <= i * (mat.cols as int) + jj < result.len() as int
                        &&& result@[(i * (mat.cols as int) + jj) as int] == mat.get(i, jj as usize)
                    },
            decreases mat.cols - j
        {
            proof {
                lemma_flatten_index_bounds(i as int, j as int, mat.rows, mat.cols);
                assert(i < mat.data.len());
                assert(j < mat.data[i].len()) by {
                    assert(mat.valid());
                    assert(0 <= i < mat.rows);
                    assert(mat.data[i].len() == mat.cols);
                };
            }
            result.push(mat.data[i][j]);
            j += 1;
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}