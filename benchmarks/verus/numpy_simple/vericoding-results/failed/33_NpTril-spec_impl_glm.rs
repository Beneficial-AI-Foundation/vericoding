// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
type Matrix<T> = Vec<Vec<T>>;

spec fn matrix_size<T>(m: Matrix<T>) -> nat {
    (m.len() * (if m.len() > 0 { m[0].len() } else { 0 })) as nat
}

fn tril(arr: Matrix<i8>, k: i8) -> (ret: Matrix<i8>)
    requires 
        arr.len() > 0,
        arr[0].len() > 0,
        -((arr.len() as i8) - 1) < k && k < (arr[0].len() as i8) - 1,
    ensures
        matrix_size(ret) == matrix_size(arr),
        ret.len() == arr.len(),
        forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr[0].len() ==> 
                if j - i > k as int { ret[i][j] == 0 } else { ret[i][j] == arr[i][j] }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed int type usage in executable code */
    let rows = arr.len();
    let cols = arr[0].len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    for i in 0..rows
        invariant
            result.len() == i,
            forall|row_idx: int| 0 <= row_idx < i ==> 
                result@[row_idx].len() == cols,
            forall|row_idx: int| 0 <= row_idx < i ==> 
                forall|col_idx: int| 0 <= col_idx < cols ==>
                    if col_idx - row_idx > k as int { result@[row_idx]@[col_idx] == 0 } else { result@[row_idx]@[col_idx] == arr@[row_idx]@[col_idx] },
    {
        let mut row = Vec::new();
        for j in 0..cols
            invariant
                row.len() == j,
                forall|col_idx: int| 0 <= col_idx < j ==>
                    if col_idx - (i as int) > k as int { row@[col_idx] == 0 } else { row@[col_idx] == arr@[i as int]@[col_idx] },
        {
            if (j as i8 - i as i8) > k {
                row.push(0);
            } else {
                row.push(arr[i][j]);
            }
        }
        result.push(row);
    }
    result
}
// </vc-code>


}
fn main() {}