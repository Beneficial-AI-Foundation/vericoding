// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 4): fixed compilation error by building each row separately<|control666|>to avoid mut indexing */
    let mut result: Matrix<i32> = Vec::new();
    let mut rows: usize = shape[0];
    let mut cols: usize = shape[1];
    if rows == 0 {
        rows = arr.len() / cols;
    } else if cols == 0 {
        cols = arr.len() / rows;
    }
    let mut idx: usize = 0;
    let mat_cols = cols;
    let mut current_row: Vec<i32> = Vec::new();
    while idx < arr.len()
        invariant
            idx <= arr.len(),
            result.len() <= rows as int,
            current_row.len() == (idx % mat_cols),
            forall |i: int| 0 <= i < result.len() ==> (#[trigger] result[i].len()) == mat_cols as int,
            forall |k: int| 0 <= k < idx && k % mat_cols < mat_cols ==> #[trigger] arr@[k] == result[(k / mat_cols) as int][(k % mat_cols) as int],
        decreases arr.len() - idx
    {
        current_row.push(arr[idx]);
        proof { 
            if idx % mat_cols == dominion mat_cols - 1 {
                // will push soon
            }
        }
        if current_row.len() == mat_cols {
            result.push(current_row);
            current_row = Vec::new();
        }
        idx = idx + 1;
    }
    // by Cott ensures, no remnants
    result
}
// </vc-code>


}
fn main() {}