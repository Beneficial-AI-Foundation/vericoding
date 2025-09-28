// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix type casting issues with int/nat conversions */
// Helper: Returns the number of rows in the matrix
spec fn rows(mat: Vec<Vec<i8>>) -> nat {
    mat@.len()
}

// Helper: Returns the number of columns in the matrix (assumes all rows same length)
spec fn cols(mat: Vec<Vec<i8>>) -> nat {
    if rows(mat) > 0 { mat@[0].len() } else { 0 }
}

// Helper lemma: All rows have same length as first row
proof fn rows_equal_length(mat: Vec<Vec<i8>>)
    requires 
        mat@.len() > 0,
        forall|i: int| 0 <= i < mat@.len() ==> mat@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < mat@.len() && 0 <= j < mat@.len() ==> mat@[i].len() == mat@[j].len()
    ensures
        forall|i: int| 0 <= i < rows(mat) ==> mat@[i].len() == cols(mat)
{
    assert(forall|i: int| 0 <= i < rows(mat) ==> mat@[i].len() == mat@[0].len());
}
// </vc-helpers>

// <vc-spec>
fn flatten(mat: Vec<Vec<i8>>) -> (result: Vec<i8>)
    requires 
        mat@.len() > 0,
        forall|i: int| 0 <= i < mat@.len() ==> mat@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < mat@.len() && 0 <= j < mat@.len() ==> mat@[i].len() == mat@[j].len(),
    ensures 
        result@.len() == mat@.len() * mat@[0].len(),
        forall|r: int, c: int| 
            0 <= r < mat@.len() && 0 <= c < mat@[0].len() ==>
            result@[r * mat@[0].len() + c] == mat@[r][c]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix index casting issues and verification bypasses */
{
    rows_equal_length(mat);
    
    let n: usize = mat.len();
    let m: usize = mat[0].len();
    let total_len = n * m;
    
    let mut result: Vec<i8> = Vec::with_capacity(total_len);
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            result@.len() == (i as int) * (m as int),
            forall|r: int, c: int| 
                0 <= r < (i as int) && 0 <= c < (m as int) ==> 
                result@[r * (m as int) + c] == mat@[r][c]
    {
        let mut j: usize = 0;
        let row = &mat[i];
        
        while j < m
            invariant
                j <= m,
                result@.len() == (i as int) * (m as int) + (j as int),
                forall|c: int| 
                    0 <= c < (j as int) ==> 
                    result@[(i as int) * (m as int) + c] == row@[c],
                forall|r: int, c: int| 
                    0 <= r < (i as int) && 0 <= c < (m as int) ==> 
                    result@[r * (m as int) + c] == mat@[r][c]
        {
            result.push(row[j]);
            j += 1;
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}