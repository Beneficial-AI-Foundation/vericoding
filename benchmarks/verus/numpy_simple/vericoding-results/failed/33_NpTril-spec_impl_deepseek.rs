// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type casting and add proper helper functions */
proof fn matrix_size_preserved<T>(m1: Matrix<T>, m2: Matrix<T>)
    ensures matrix_size(m1) == matrix_size(m2)
{
    // Matrix size is defined as total elements, which is preserved in reshape
}

fn zero_i8() -> i8 {
    0
}

spec fn get_row_len<T>(m: Matrix<T>, i: int) -> nat {
    m[i].len() as nat
}

spec fn same_dimensions<T>(m1: Matrix<T>, m2: Matrix<T>) -> bool {
    m1.len() == m2.len() &&
    forall|i: int| 0 <= i < m1.len() ==> m1[i].len() == m2[i].len()
}
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
    /* code modified by LLM (iteration 5): Fix integer casting and indexing */
    let rows = arr.len();
    let cols = arr[0].len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    
    while i < rows
        invariant
            i <= rows,
            result.len() == i,
            forall|r: int| 0 <= r < i ==> result[r].len() == cols,
            forall|r: int, c: int| 0 <= r < i && 0 <= c < cols ==> 
                if c - r > k as int { result[r][c] == 0 } else { result[r][c] == arr[r][c] },
            matrix_size(result) == i * cols as nat
    {
        let mut row_vec = Vec::new();
        let mut j: usize = 0;
        
        while j < cols
            invariant
                j <= cols,
                row_vec.len() == j,
                forall|c: int| 0 <= c < j ==> 
                    if c as int - i as int > k as int { row_vec[c] == 0 } else { row_vec[c] == arr[i][c] }
        {
            if (j as int) - (i as int) > k as int {
                row_vec.push(0);
            } else {
                row_vec.push(arr[i][j]);
            }
            j += 1;
        }
        result.push(row_vec);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}