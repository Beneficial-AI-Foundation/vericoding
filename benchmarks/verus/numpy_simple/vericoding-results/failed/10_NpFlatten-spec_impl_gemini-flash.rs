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
/* helper modified by LLM (iteration 5): [brief description] */
pub open spec fn get_flat_idx(i: int, j: int, cols: int) -> int
    recommends
        i >= 0,
        j >= 0,
        cols > 0
{
    i * cols + j
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
/* code modified by LLM (iteration 5): [Fixed invariants to use helper function and account for current row.] */
{
    let mut flat_vec: Vec<i32> = Vec::new();
    let mut r_idx: usize = 0;

    while r_idx < mat.rows
        invariant
            r_idx <= mat.rows,
            flat_vec.len() == (r_idx as nat) * (mat.cols as nat),
            forall|i: int, j: int|
                0 <= i && i < r_idx as int && 0 <= j && j < mat.cols as int ==> 
                #[trigger] flat_vec@[get_flat_idx(i, j, mat.cols as int)] == mat.data[i as int][j as int],
            mat.valid(),
            mat.cols > 0,
        decreases mat.rows - r_idx
    {
        let mut c_idx: usize = 0;
        while c_idx < mat.cols
            invariant
                r_idx < mat.rows,
                c_idx <= mat.cols,
                flat_vec.len() == (r_idx as nat) * (mat.cols as nat) + (c_idx as nat),
                forall|i: int, j: int|
                    0 <= i && i < r_idx as int && 0 <= j && j < mat.cols as int ==> 
                    #[trigger] flat_vec@[get_flat_idx(i, j, mat.cols as int)] == mat.data[i as int][j as int],
                forall|j_prime: int|
                    0 <= j_prime && j_prime < c_idx as int ==> 
                    #[trigger] flat_vec@[get_flat_idx(r_idx as int, j_prime, mat.cols as int)] == mat.data[r_idx as int][j_prime as int],
                mat.valid(),
                mat.cols > 0,
            decreases mat.cols - c_idx
        {
            let val = mat.data[r_idx][c_idx];
            flat_vec.push(val);
            c_idx = c_idx + 1;
        }
        r_idx = r_idx + 1;
    }
    flat_vec
}
// </vc-code>


}
fn main() {}