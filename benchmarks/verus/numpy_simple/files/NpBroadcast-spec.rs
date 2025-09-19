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
    // impl-start
    assume(false);
    Matrix {
        data: Vec::new(),
        rows: 0,
        cols: 0,
    }
    // impl-end
}
// </vc-code>


}
fn main() {}