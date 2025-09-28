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

fn seq_flatten(mat: Matrix, i: int) -> Seq<i32> 
    requires 
        0 <= i <= mat.rows, 
        mat.valid(), 
    ensures 
        result.len() == i * (mat.cols as int), 
        forall|k: int, l: int| 0 <= k < i && 0 <= l < mat.cols as int ==> 
            #[trigger] result@[k * (mat.cols as int) + l] == mat.get(k as usize, l as usize), 
    decreases mat.rows - i, 
{
    if i == 0 {
        Seq::empty()
    } else {
        let prev = seq_flatten(mat, i - 1);
        let row = mat.data@[i - 1].view();
        prev + row
    }
}

proof fn lemma_flatten_properties(mat: Matrix, i: int) 
    requires 
        0 <= i <= mat.rows, 
        mat.valid(), 
    ensures 
        seq_flatten(mat, i).len() == i * (mat.cols as int), 
        forall|k: int, l: int| 0 <= k < i && 0 <= l < mat.cols as int ==> 
            #[trigger] seq_flatten(mat, i)@[k * (mat.cols as int) + l] == mat.get(k as usize, l as usize), 
{
    reveal_with_fuel(seq_flatten, 3);
    if i > 0 {
        lemma_flatten_properties(mat, i - 1);
    }
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
    /* code modified by LLM (iteration 5): Fixed result variable name to match return spec */
    let mut ret = Vec::<i32>::new();
    let mut i: usize = 0;
    while i < mat.rows
        invariant
            i <= mat.rows,
            ret.len() == i * mat.cols,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < mat.cols as int ==> 
                #[trigger] ret@[k * (mat.cols as int) + l] == mat.get(k as usize, l as usize),
        decreases mat.rows - i,
    {
        let mut j: usize = 0;
        while j < mat.cols
            invariant
                j <= mat.cols,
                ret.len() == i * mat.cols + j,
                forall|k: int, l: int| 0 <= k < i && 0 <= l < mat.cols as int ==> 
                    #[trigger] ret@[k * (mat.cols as int) + l] == mat.get(k as usize, l as usize),
                forall|l: int| 0 <= l < j ==> 
                    #[trigger] ret@[i * (mat.cols as int) + l] == mat.get(i, l as usize),
            decreases mat.cols - j,
        {
            ret.push(mat.get(i, j));
            j += 1;
        }
        i += 1;
    }
    ret
}
// </vc-code>


}
fn main() {}