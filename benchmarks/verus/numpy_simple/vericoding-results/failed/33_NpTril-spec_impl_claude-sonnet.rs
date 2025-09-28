// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_valid_matrix<T>(m: Matrix<T>) -> bool {
    m.len() > 0 && (forall|i: int| #[trigger] m[i].len() 0 <= i < m.len() ==> m[i].len() == m[0].len())
}

/* helper modified by LLM (iteration 5): fixed lemma syntax by removing 'lemma' keyword */
proof fn matrix_indexing_lemma<T>(m: Matrix<T>, i: int, j: int)
    requires
        is_valid_matrix(m),
        0 <= i < m.len(),
        0 <= j < m[0].len(),
    ensures
        0 <= i < m.len() && 0 <= j < m[i].len(),
{
}

/* helper modified by LLM (iteration 5): fixed lemma syntax by removing 'lemma' keyword */
proof fn matrix_size_preservation_lemma<T>(original: Matrix<T>, result: Matrix<T>)
    requires
        is_valid_matrix(original),
        result.len() == original.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == original[0].len(),
    ensures
        matrix_size(result) == matrix_size(original),
{
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
    /* code modified by LLM (iteration 5): added decreases clause to outer loop */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result.len() == i,
            forall|row_idx: int| 0 <= row_idx < i ==> result[row_idx].len() == arr[0].len(),
            forall|row_idx: int, col_idx: int| 
                0 <= row_idx < i && 0 <= col_idx < arr[0].len() ==>
                    if col_idx - row_idx > k as int { 
                        result[row_idx][col_idx] == 0 
                    } else { 
                        result[row_idx][col_idx] == arr[row_idx][col_idx] 
                    },
        decreases arr.len() - i
    {
        let mut row = Vec::new();
        let mut j = 0;
        
        while j < arr[0].len()
            invariant
                0 <= i < arr.len(),
                0 <= j <= arr[0].len(),
                row.len() == j,
                forall|col_idx: int| 
                    0 <= col_idx < j ==>
                        if col_idx - (i as int) > k as int { 
                            row[col_idx] == 0 
                        } else { 
                            row[col_idx] == arr[i as int][col_idx] 
                        },
            decreases arr[0].len() - j
        {
            if (j as i8) - (i as i8) > k {
                row.push(0);
            } else {
                row.push(arr[i][j]);
            }
            j += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}