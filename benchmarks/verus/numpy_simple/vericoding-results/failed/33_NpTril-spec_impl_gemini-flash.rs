// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unused imports, as the `index` operation is provided by Verus's `vstd::vec::Vec`. */

fn create_zero_matrix<T: Copy>(rows: usize, cols: usize, default_val: T) -> (ret: Matrix<T>)
    requires
        rows == 0 || cols == 0 || rows * cols < usize::MAX,
    ensures
        ret.len() == rows,
        rows > 0 ==> ret@[0].len() == cols,
        forall|i: int, j: int|
            0 <= i < rows && 0 <= j < cols ==> ret[i][j] == default_val,
{
    let mut new_matrix: Vec<Vec<T>> = Vec::new();
    let mut r_idx: usize = 0;
    while r_idx < rows
        invariant
            r_idx <= rows,
            new_matrix.len() == r_idx,
            forall|i: int|
                0 <= i < r_idx ==> new_matrix[i].len() == cols,
            forall|i: int, j: int|
                0 <= i < r_idx && 0 <= j < cols ==> new_matrix[i][j] == default_val,
        decreases rows - r_idx
    {
        let mut new_row: Vec<T> = Vec::new();
        let mut c_idx: usize = 0;
        while c_idx < cols
            invariant
                c_idx <= cols,
                new_row.len() == c_idx,
                forall|k: int|
                    0 <= k < c_idx ==> new_row[k] == default_val,
            decreases cols - c_idx
        {
            new_row.push(default_val);
            c_idx = c_idx + 1;
        }
        new_matrix.push(new_row);
        r_idx = r_idx + 1;
    }
    new_matrix
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
/* code modified by LLM (iteration 5): Fixed a compilation error where `set_index` was incorrectly called on a mutable reference to a `Vec`, which does not have that method. Instead, direct indexing `ret[r_idx][c_idx]` is used for assignment, leveraging Verus's `vstd::vec::Vec` behavior and `IndexMut` implementation. */
{
    let rows = arr.len();
    let cols = arr[0].len();

    let mut ret = create_zero_matrix(rows, cols, 0i8);

    let mut r_idx: usize = 0;
    while r_idx < rows
        invariant
            r_idx <= rows,
            ret.len() == rows,
            ret@[0].len() == cols,
            forall|i: int, j: int|
                0 <= i < r_idx && 0 <= j < cols && j - i <= k as int ==> ret[i][j] == arr[i][j],
            forall|i: int, j: int|
                0 <= i < r_idx && 0 <= j < cols && j - i > k as int ==> ret[i][j] == 0,
            forall|i: int, j: int|
                r_idx <= i < rows && 0 <= j < cols ==> ret[i][j] == 0,
        decreases rows - r_idx
    {
        let mut c_idx: usize = 0;
        while c_idx < cols
            invariant
                c_idx <= cols,
                ret.len() == arr.len(),
                ret@[0].len() == arr@[0].len(),
                forall|i: int, j: int|
                    0 <= i < r_idx && 0 <= j < cols && j - i <= k as int ==> ret[i][j] == arr[i][j],
                forall|i: int, j: int|
                    0 <= i < r_idx && 0 <= j < cols && j - i > k as int ==> ret[i][j] == 0,
                forall|j: int|
                    0 <= j < c_idx && (j - r_idx) <= k as int ==> ret[r_idx as int][j] == arr[r_idx as int][j],
                forall|j: int|
                    0 <= j < c_idx && (j - r_idx) > k as int ==> ret[r_idx as int][j] == 0,
                forall|j: int|
                    c_idx <= j < cols ==> ret[r_idx as int][j] == 0,
                forall|i: int, j: int|
                    r_idx + 1 <= i < rows && 0 <= j < cols ==> ret[i][j] == 0,
            decreases cols - c_idx
        {
            if (c_idx as i8) - (r_idx as i8) <= k {
                ret[r_idx][c_idx] = arr[r_idx][c_idx];
            }
            c_idx = c_idx + 1;
        }
        r_idx = r_idx + 1;
    }
    ret
}
// </vc-code>


}
fn main() {}