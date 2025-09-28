// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn rows_of(arr_len: nat, s0: nat, s1: nat) -> nat {
    if s0 > 0 { s0 } else { arr_len / s1 }
}

spec fn cols_of(arr_len: nat, s0: nat, s1: nat) -> nat {
    if s1 > 0 { s1 } else { arr_len / s0 }
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
{
    let n: usize = arr.len();
    let s0: usize = shape[0];
    let s1: usize = shape[1];

    let rows: usize = if s0 > 0 { s0 } else { n / s1 };
    let cols: usize = if s1 > 0 { s1 } else { n / s0 };

    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut idx: usize = 0;
    let mut r: usize = 0;

    while r < rows
        invariant
            r <= rows,
            idx == r * cols,
            result.len() == r,
            forall|rr: usize| rr < r ==> forall|cc: usize| cc < cols ==> result[rr][cc] == arr[rr * cols + cc],
        decreases rows - r
    {
        let mut row_vec: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < cols
            invariant
                c <= cols,
                idx == r * cols + c,
                row_vec.len() == c,
                forall|cc: usize| cc < c ==> row_vec[cc] == arr[r * cols + cc],
            decreases cols - c
        {
            row_vec.push(arr[idx]);
            idx = idx + 1;
            c = c + 1;
        }
        result.push(row_vec);
        r = r + 1;
    }

    proof {
        // show rows * cols == n
        if s0 > 0 && s1 > 0 {
            assert(rows == s0);
            assert(cols == s1);
            // precondition guarantees s0 * s1 == arr.len()
            assert(rows * cols == n);
        } else if s0 == 0 {
            assert(rows == n / s1);
            assert(cols == s1);
            // use division remainder property and precondition arr.len() % s1 == 0
            assert(n == (n / s1) * s1 + n % s1);
            assert(n % s1 == 0);
            assert(n == (n / s1) * s1);
            assert(rows * cols == n);
        } else {
            // s1 == 0
            assert(rows == s0);
            assert(cols == n / s0);
            assert(n == (n / s0) * s0 + n % s0);
            assert(n % s0 == 0);
            assert(n == (n / s0) * s0);
            assert(rows * cols == n);
        }

        // idx must equal n after filling
        assert(idx == rows * cols);
        assert(idx == n);

        // Now prove the element correspondence
        assert(forall|rr: usize| rr < rows ==> forall|cc: usize| cc < cols ==> result[rr][cc] == arr[rr * cols + cc]);
        assert(forall|i: nat| i < (n as nat) ==>
            {
                let rr: usize = (i as usize) / cols;
                let cc: usize = (i as usize) % cols;
                result[rr][cc] == arr[rr * cols + cc]
            }
        );
        assert(forall|i: nat| i < (n as nat) ==>
            get_vector_element(arr@, i) == result[((i as usize) / cols) as int][((i as usize) % cols) as int]
        );
    }

    result
}
// </vc-code>


}
fn main() {}