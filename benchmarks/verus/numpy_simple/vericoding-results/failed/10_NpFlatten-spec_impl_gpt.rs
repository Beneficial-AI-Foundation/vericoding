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
/* helper modified by LLM (iteration 2): prove row-major index order across rows */
proof fn lemma_prev_row_index_lt(i0: int, i: int, cols: int, j0: int)
    requires
        0 <= cols,
        0 <= j0 < cols,
        0 <= i0 < i,
    ensures
        i0 * cols + j0 < i * cols,
{
    // From 0 <= j0 < cols and 0 <= cols, we get:
    assert(i0 * cols + j0 < i0 * cols + cols);
    // i0 * cols + cols equals (i0 + 1) * cols
    assert(i0 * cols + cols == (i0 + 1) * cols);
    // From i0 < i, we have i0 + 1 <= i
    assert(i0 + 1 <= i);
    // Since cols >= 0 and i0 + 1 <= i, multiplying preserves inequality
    assert((i0 + 1) * cols <= i * cols);
    // Chain inequalities to conclude
    // i0 * cols + j0 < (i0 + 1) * cols <= i * cols
}

/* helper modified by LLM (iteration 2): relate get() to underlying data indexing (int indices) */
proof fn lemma_get_equals_data_index(mat: &Matrix, i: usize, j: usize)
    requires
        mat.valid(),
        i < mat.rows,
        j < mat.cols,
    ensures
        mat.get(i, j) == mat.data[i as int][j as int],
{
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
    /* code modified by LLM (iteration 2): implement flatten with nested loops; fix int/usize usage in proofs */
    let mut ret: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < mat.rows
        invariant
            mat.valid(),
            mat.rows > 0,
            mat.cols > 0,
            i <= mat.rows,
            ret.len() == i * mat.cols,
            forall|ii: int, jj: int|
                0 <= ii < i && 0 <= jj < mat.cols ==> #[trigger] ret@[(ii * (mat.cols as int) + jj) as int] == mat.get(ii as usize, jj as usize),
        decreases mat.rows - i
    {
        let mut j: usize = 0;
        while j < mat.cols
            invariant
                mat.valid(),
                mat.rows > 0,
                mat.cols > 0,
                i < mat.rows,
                j <= mat.cols,
                ret.len() == i * mat.cols + j,
                forall|ii: int, jj: int|
                    0 <= ii < i && 0 <= jj < mat.cols ==> #[trigger] ret@[(ii * (mat.cols as int) + jj) as int] == mat.get(ii as usize, jj as usize),
                forall|jj: int|
                    0 <= jj < j ==> #[trigger] ret@[(((i as int) * (mat.cols as int) + jj) as int)] == mat.get(i as usize, jj as usize),
            decreases mat.cols - j
        {
            // Safety proofs for indexing
            proof {
                assert(mat.data.len() == mat.rows);
                assert(i < mat.data.len());
                let ii: int = i as int;
                assert(0 <= ii && ii < mat.rows);
                assert(mat.data[ii].len() == mat.cols);
                assert(j < mat.cols);
                assert(j < mat.data[ii].len());
            }
            let val = mat.data[i][j];

            // Prepare for push: remember old sequence and index
            let old_len_int: int = ret.len() as int;
            let old_seq = ret@;
            ret.push(val);
            proof {
                assert(ret@ == old_seq.push(val));
                let idx: int = (i as int) * (mat.cols as int) + (j as int);
                assert(old_len_int == idx);
                assert(ret@[idx] == val);
                // Connect value to spec get
                lemma_get_equals_data_index(mat, i, j);
                assert(val == mat.get(i, j));
            }
            j = j + 1;
        }
        i = i + 1;
    }
    ret
}
// </vc-code>


}
fn main() {}