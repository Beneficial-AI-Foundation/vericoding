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
    let rows = if shape[0] == 0 { arr.len() / shape[1] } else { shape[0] };
    let cols = if shape[1] == 0 { arr.len() / shape[0] } else { shape[1] };
    let mut result: Matrix<i32> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant 
            i <= rows,
            result.len() == i,
            forall|r: nat| r < (i as nat) ==> 
                forall|c: nat| c < (cols as nat) ==> 
                    result[r][c] == arr@[r * (cols as nat) + c],
        decreases (rows - i) as nat
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant 
                j <= cols,
                row.len() == j,
                forall|c: nat| c < (j as nat) ==> 
                    row[c] == arr@[(i as nat) * (cols as nat) + c],
            decreases (cols - j) as nat
        {
            row.push(arr[i * cols + j]);
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