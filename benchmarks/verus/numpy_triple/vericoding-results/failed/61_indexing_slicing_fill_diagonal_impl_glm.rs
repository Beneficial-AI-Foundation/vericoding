// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fill_diagonal<T: Copy>(mat: Vec<Vec<T>>, val: T) -> (result: Vec<Vec<T>>)
    requires 
        mat@.len() > 0,
        forall|i: int| 0 <= i < mat@.len() ==> #[trigger] mat@[i].len() == mat@[0].len(),
    ensures
        result@.len() == mat@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i].len() == mat@[i].len(),

        forall|i: int, j: int| 
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i == j 
            ==> #[trigger] result@[i][j] == val,

        forall|i: int, j: int| 
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i != j 
            ==> #[trigger] result@[i][j] == mat@[i][j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error in inner loop invariant by replacing mat@.len() with mat.len() as int */
{
    let n = mat.len();
    let m = mat[0].len();
    let mut result: Vec<Vec<T>> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            i as int <= mat@.len(),
            result@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> #[trigger] result@[k].len() == m as int,
            forall|k: int, l: int| 
                0 <= k < i as int && 0 <= l < m as int && k == l 
                ==> #[trigger] result@[k][l] == val,
            forall|k: int, l: int| 
                0 <= k < i as int && 0 <= l < m as int && k != l 
                ==> #[trigger] result@[k][l] == mat@[k][l],
        decreases n - i
    {
        let mut row = Vec::new();
        let mut j = 0usize;
        while j < m
            invariant
                j <= m,
                row@.len() == j as int,
                i as int < mat.len() as int,
                j as int < mat[i].len() as int,
                forall|l: int| 0 <= l < j as int ==> (i as int == l ==> row@[l] == val),
                forall|l: int| 0 <= l < j as int ==> (i as int != l ==> row@[l] == mat@[i as int][l]),
            decreases m - j
        {
            if i == j {
                row.push(val);
            } else {
                row.push(mat[i][j]);
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