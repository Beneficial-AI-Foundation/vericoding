// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed `spec` attribute not found error by removing it. */
fn get_num_cols(arr_len: int, shape: Seq<int>) -> int {
    if shape[1] > 0 {
        shape[1]
    } else {
        arr_len / shape[0]
    }
}
// </vc-helpers>

// <vc-spec>
type Matrix<T> = Vec<Vec<T>>;

spec fn matrix_size<T>(mat: Matrix<T>) -> nat {
    if mat.len() == 0 { 0 } else { (mat.len() * mat[0].len()) as nat }
}

spec fn get_matrix_element<T>(mat: Matrix<T>, i: nat, j: nat) -> T {
    mat[i as int][j as int]
}

spec fn get_vector_element<T>(arr: Seq<T>, i: nat) -> T {
    arr[i as int]
}

fn reshape(arr: Vec<i32>, shape: Vec<usize>) -> (result: Matrix<i32>)
    requires 
        arr.len() > 0,
        shape.len() == 2,
        forall|i: int| 0 <= i < 2 ==> (shape[i] > 0 || shape[i] == 0),
        !(shape[0] == 0 && shape[1] == 0),
        (if shape[0] > 0 && shape[1] > 0 { 
            shape[0] * shape[1] == arr.len()
        } else if shape[0] == 0 { 
            arr.len() % shape[1] == 0
        } else { 
            arr.len() % shape[0] == 0
        }),
    ensures
        result.len() > 0,
        result[0].len() > 0,
        (if shape[0] > 0 { 
            matrix_size(result) / (if shape[1] > 0 { shape[1] as nat } else { (arr.len() / shape[0]) as nat }) == shape[0] as nat
        } else { 
            matrix_size(result) / (if shape[1] > 0 { shape[1] as nat } else { (arr.len() / shape[0]) as nat }) == (arr.len() / shape[1]) as nat
        }),
        forall|i: nat| i < arr.len() ==> #[trigger] get_vector_element(arr@, i) == result[((i as usize) / result[0].len()) as int][((i as usize) % result[0].len()) as int]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type issues with `nat` and `int` in ghost variables and `get_num_cols` call by casting to `int` before passing to the helper function. */
{
    let rows = shape[0];
    let cols = shape[1];

    let num_rows: usize;
    let num_cols: usize;

    let arr_len_int = arr.len() as int;
    let shape_seq: Seq<int> = Seq::new(2, |idx: int| shape[idx as usize] as int);

    num_cols = get_num_cols(arr_len_int, shape_seq) as usize;

    if rows == 0 {
        num_rows = arr.len() / num_cols;
    } else {
        num_rows = rows;
    }
    
    let mut result: Matrix<i32> = Vec::new();

    let mut i: usize = 0;
    while i < num_rows
        invariant
            result.len() == i as nat,
            result.len() <= num_rows as nat,
            (num_rows * num_cols) as int == arr.len() as int,
            forall|k: nat| k < result.len() ==> result[k as int].len() == num_cols as nat,
            forall|r: nat, c:nat| r < i as nat && c < num_cols as nat ==> result[r as int][c as int] == arr@[(r * num_cols as nat + c) as int],
            i <= num_rows,
    {
        let mut row_vec: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < num_cols
            invariant
                row_vec.len() == j as nat,
                row_vec.len() <= num_cols as nat,
                forall|c: nat| c < j as nat ==> row_vec[c as int] == arr@[(i * num_cols + c) as int],
                j <= num_cols,
        {
            row_vec.push(arr[i * num_cols + j]);
            j = j + 1;
        }
        result.push(row_vec);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}