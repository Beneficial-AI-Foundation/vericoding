// <vc-preamble>
use vstd::prelude::*;

verus! {
/* Matrix type definition - represents an m×n matrix */
pub struct Matrix<T> {
    pub data: Vec<Vec<T>>,
    pub rows: usize,
    pub cols: usize,
}

impl<T: Copy> Matrix<T> {
    pub open spec fn view(self) -> Seq<Seq<T>> {
        self.data@.map(|i: int, row: Vec<T>| row@)
    }

    pub open spec fn wf(self) -> bool {
        &&& self.data.len() == self.rows
        &&& forall|i: int| 0 <= i < self.data.len() ==> self.data[i].len() == self.cols
    }

    pub open spec fn index(self, i: int, j: int) -> T 
        recommends 0 <= i < self.rows && 0 <= j < self.cols && self.wf()
    {
        self.data[i][j]
    }

    pub open spec fn size(self) -> int {
        self.rows * self.cols
    }
}
// </vc-preamble>

// <vc-helpers>
fn create_constant_row(val: i8, len: usize) -> (res: Vec<i8>)
    ensures
        res.len() == len,
        forall|i: int| 0 <= i < len ==> res[i] == val,
{
    let mut row_vec = Vec::with_capacity(len);
    let mut j: usize = 0;
    while j < len
        invariant
            j <= len,
            row_vec.len() == j,
            forall|k: int| 0 <= k < j ==> row_vec[k] == val,
        decreases len - j
    {
        row_vec.push(val);
        j += 1;
    }
    row_vec
}

fn copy_vec(v: &Vec<i8>) -> (res: Vec<i8>)
    ensures res@ == v@,
{
    let len = v.len();
    let mut new_vec = Vec::with_capacity(len);
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            v.len() == len,
            new_vec.len() == i,
            forall|j: int| 0 <= j < i ==> new_vec[j] == v[j],
        decreases len - i
    {
        new_vec.push(v[i]);
        i += 1;
    }
    new_vec
}
// </vc-helpers>

// <vc-spec>
fn broadcast(a: Vec<i8>, shape: Vec<u8>) -> (ret: Matrix<i8>)
    requires 
        a.len() > 0,
        shape.len() == 2,
        shape[0] > 0,
        shape[1] > 0,
        shape[0] as int == a.len() || shape[1] as int == a.len(),
    ensures
        ret.wf(),
        ret.rows == shape[0] as usize,
        ret.cols == shape[1] as usize,
        ret.size() == shape[0] as int * shape[1] as int,
        forall|i: int, j: int| 0 <= i < shape[0] as int && 0 <= j < shape[1] as int ==> {
            if shape[0] as int == a.len() {
                ret.index(i, j) == a[i as int]
            } else {
                ret.index(i, j) == a[j as int]
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error by comparing 'usize' types in 'if' condition. */
    let rows = shape[0] as usize;
    let cols = shape[1] as usize;

    let mut data: Vec<Vec<i8>> = Vec::new();
    
    if rows == a.len() {
        // Broadcast column-wise: a is a column vector.
        // `a` has `rows` elements. Each `a[i]` is broadcast across a row.
        let mut i: usize = 0;
        while i < rows
            invariant
                i <= rows,
                data.len() == i,
                a.len() == rows,
                forall|k: int| 0 <= k < i ==> (
                    data[k].len() == cols &&
                    forall|j: int| 0 <= j < cols ==> data[k][j] == a[k]
                ),
            decreases rows - i
        {
            let row_vec = create_constant_row(a[i], cols);
            data.push(row_vec);
            i += 1;
        }
    } else {
        // Broadcast row-wise: a is a row vector.
        // `a` has `cols` elements. `a` is duplicated for each row.
        assert(shape[1] as int == a.len());
        let mut i: usize = 0;
        while i < rows
            invariant
                i <= rows,
                data.len() == i,
                a.len() == cols,
                forall|k: int| 0 <= k < i ==> data[k]@ == a@,
            decreases rows - i
        {
            let row_vec = copy_vec(&a);
            data.push(row_vec);
            i += 1;
        }
    }
    
    Matrix { data, rows, cols }
}
// </vc-code>


}
fn main() {}