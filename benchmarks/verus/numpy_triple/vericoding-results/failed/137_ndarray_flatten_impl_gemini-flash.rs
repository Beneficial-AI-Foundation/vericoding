// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The current iteration's implementation of the flatten function produces a compilation error where 'nat' cannot be used in ghost code. This error occurs because variable `cols` is declared as `nat` in ghost code. `cols` is being initialized using non-ghost context (`mat@.index(0).len()`). This is an issue in the variable declaration, not in the `flatten` function implementation logic. To resolve the compilation error, I am introducing a helper function, that converts the matrix to a ghost matrix for use in the body (and will allow the definition of `cols` to proceed without triggering errors). */
fn get_ghost_matrix(mat: Vec<Vec<i8>>) -> (ghost_mat: Ghost<Seq<Seq<i8>>>)
    ensures
        ghost_mat@.len() == mat@.len(),
        forall|i: int| 0 <= i < mat@.len() ==> ghost_mat@[i].len() == mat@[i].len(),
        forall|i: int, j: int| 0 <= i < mat@.len() && 0 <= j < mat@[i].len() ==> 
        ghost_mat@[i]@[j] == mat@[i]@[j]
{
    let mut ghost_rows = Seq::<Seq<i8>>::new();
    let mut i = 0;
    while i < mat@.len()
        invariant
            0 <= i <= mat@.len(),
            ghost_rows.len() == i,
            forall|k: int| 0 <= k < i ==> ghost_rows[k].len() == mat@[k].len(),
            forall|k: int, l: int| 0 <= k < i && 0 <= l < mat@[k].len()
                ==> ghost_rows[k][l] == mat@[k]@[l],
    {
        let mut ghost_cols = Seq::<i8>::new();
        let mut j = 0;
        while j < mat@[i].len()
            invariant
                0 <= j <= mat@[i].len(),
                ghost_cols.len() == j,
                forall|k: int| 0 <= k < j ==> ghost_cols[k] == mat@[i]@[k],
        {
            ghost_cols = ghost_cols.push(mat@[i]@[j]);
            j = j + 1;
        }
        ghost_rows = ghost_rows.push(ghost_cols);
        i = i + 1;
    }
    Ghost(ghost_rows)
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
/* code modified by LLM (iteration 5): Fixed compilation error by moving the `nat` variable `cols` definitions into a helper function inside ghost code. Also converting the `nat` type for the `index` variable into `int` to allow access on `Vec`s through a `into()` type conversion. */
{
    let ghost_mat = get_ghost_matrix(mat.clone());
    let rows: nat = mat@.len();
    let cols: nat = ghost_mat@.index(0).len() as nat;
    let mut result = Vec::<i8>::new();
    result.reserve((rows * cols) as usize);

    let mut r_idx: nat = 0;
    while r_idx < rows
        invariant
            result@.len() == r_idx * cols as int,
            forall|r_inv: int, c_inv: int|
                0 <= r_inv < r_idx && 0 <= c_inv < cols ==> result@[r_inv * cols as int + c_inv] == mat@[r_inv][c_inv],
            0 <= r_idx <= rows,
            0 <= cols,
        decreases rows - r_idx
    {
        let mut c_idx: nat = 0;
        while c_idx < cols
            invariant
                result@.len() == r_idx * cols as int + c_idx as int,
                forall|r_inner: int, c_inner: int|
                    0 <= r_inner < r_idx && 0 <= c_inner < cols ==> result@[r_inner * cols as int + c_inner] == mat@[r_inner][c_inner],
                forall|c_inner: int|
                    0 <= c_inner < c_idx ==> result@[r_idx * cols as int + c_inner] == mat@[r_idx as int][c_inner],
                0 <= r_idx < rows,
                0 <= c_idx <= cols,
                0 <= cols,
            decreases cols - c_idx
        {
            result.push(mat[r_idx.into()][c_idx.into()]);
            c_idx = c_idx + 1;
        }
        r_idx = r_idx + 1;
    }

    result
}
// </vc-code>

}
fn main() {}