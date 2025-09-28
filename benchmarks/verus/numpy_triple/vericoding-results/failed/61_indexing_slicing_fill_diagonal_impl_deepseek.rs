// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed int/nat type error by using uint_to_int conversion */
fn fill_diagonal_inner<T: Copy>(mat: &Vec<Vec<T>>, val: T, i: usize) -> (result_row: Vec<T>)
    requires
        0 <= i < mat@.len(),
        mat@[i].len() == mat@[0].len()
    ensures
        result_row@.len() == mat@[i].len(),
        forall|j: int| 0 <= j < result_row@.len() && i as int == j ==> #[trigger] result_row@[j] == val,
        forall|j: int| 0 <= j < result_row@.len() && i as int != j ==> #[trigger] result_row@[j] == mat@[i][j]
{
    let mut new_row: Vec<T> = Vec::new();
    let i_int = i as int;
    let mut k: usize = 0;

    while k < mat@[i].len() as usize
        invariant
            0 <= k <= mat@[i].len() as usize,
            new_row@.len() == k as int,
            forall|j: int| 0 <= j < k as int && i_int == j ==> #[trigger] new_row@[j] == val,
            forall|j: int| 0 <= j < k as int && i_int != j ==> #[trigger] new_row@[j] == mat@[i][j]
        decreases (mat@[i].len() as usize) - k
    {
        let j_int = k as int;
        if j_int == i_int {
            new_row.push(val);
        } else {
            new_row.push(mat[i][k]);
        }
        k = k + 1;
    }
    new_row
}
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
/* code modified by LLM (iteration 5): fixed int/nat type error by using usize indexing */
{
    let mut result: Vec<Vec<T>> = Vec::with_capacity(mat@.len() as usize);
    let mut i: usize = 0;

    while i < mat@.len() as usize
        invariant
            0 <= i as int <= mat@.len(),
            result@.len() == i as int,
            forall|r: int| 0 <= r < i as int ==> result@[r].len() == mat@[r].len(),
            forall|r: int, c: int| 0 <= r < i as int && 0 <= c < result@[r].len() && r == c ==> #[trigger] result@[r][c] == val,
            forall|r: int, c: int| 0 <= r < i as int && 0 <= c < result@[r].len() && r != c ==> #[trigger] result@[r][c] == mat@[r][c]
        decreases (mat@.len() as usize) - i
    {
        let new_row = fill_diagonal_inner(&mat, val, i);
        result.push(new_row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}