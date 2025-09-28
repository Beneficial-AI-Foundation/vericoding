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
    /* code modified by LLM (iteration 5): fixed compilation errors by using correct lemma names and assert syntax. */
    let s0 = shape[0];
    let s1 = shape[1];
    let n = arr.len();

    let num_rows: usize;
    let num_cols: usize;

    if s0 > 0 && s1 > 0 {
        num_rows = s0;
        num_cols = s1;
    } else if s0 == 0 {
        num_cols = s1;
        num_rows = n / num_cols;
    } else {
        num_rows = s0;
        num_cols = n / num_rows;
    }

    assert((num_rows * num_cols) as nat == n) by {
        if s0 > 0 && s1 > 0 {
            // In this case, num_rows * num_cols == s0 * s1 == n from requires.
        } else if s0 == 0 {
            // We have num_cols = s1 > 0 and n % s1 == 0.
            // We want to prove (n / num_cols) * num_cols == n.
            vstd::arithmetic::div_mod::lemma_div_by_multiple(n as int, num_cols as int);
        } else {
            // We have num_rows = s0 > 0 and n % s0 == 0.
            // We want to prove num_rows * (n / num_rows) == n.
            vstd::arithmetic::div_mod::lemma_div_by_multiple(n as int, num_rows as int);
            // The above proves (n / num_rows) * num_rows == n. We need commutativity.
            vstd::arithmetic::mul::lemma_mul_is_commutative(num_rows as int, (n / num_rows) as int);
        }
    };

    let mut result: Matrix<i32> = Vec::new();
    let mut k: usize = 0;

    while result.len() < num_rows
        invariant
            result.len() <= num_rows,
            (num_rows * num_cols) as nat == arr.len(),
            k == result.len() * num_cols,
            forall|r_idx: int| 0 <= r_idx < result.len() ==> #[trigger] result[r_idx].len() == num_cols,
            forall|r_idx: int, c_idx: int| 0 <= r_idx < result.len() && 0 <= c_idx < num_cols ==> 
                #[trigger] result[r_idx][c_idx] == arr@[(r_idx * num_cols + c_idx) as int],
        decreases num_rows - result.len()
    {
        let mut row: Vec<i32> = Vec::new();
        let start_k = k;

        while row.len() < num_cols
            invariant
                row.len() <= num_cols,
                k == start_k + row.len(),
                result.len() < num_rows,
                (num_rows * num_cols) as nat == arr.len(),
                forall|c_idx: int| 0 <= c_idx < row.len() ==> row@[c_idx] == arr@[(start_k + c_idx) as int],
            decreases num_cols - row.len()
        {
            assert(k < arr.len()) by(nonlinear_arith);
            row.push(arr[k]);
            k = k + 1;
        }
        
        proof {
            let r_idx = result.len();
            assert(start_k == r_idx * num_cols);
            assert forall|c_idx: int| 0 <= c_idx < num_cols implies
                #[trigger] row@[c_idx] == arr@[(r_idx * num_cols + c_idx) as int]
            by {}
        }

        result.push(row);
    }
    result
}
// </vc-code>


}
fn main() {}