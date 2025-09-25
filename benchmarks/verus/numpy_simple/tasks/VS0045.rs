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
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}