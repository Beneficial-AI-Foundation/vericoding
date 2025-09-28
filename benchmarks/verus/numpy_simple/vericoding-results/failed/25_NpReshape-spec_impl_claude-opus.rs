// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed ensures syntax to avoid closure-style notation */
fn compute_dimensions(arr: &Vec<i32>, shape: &Vec<usize>) -> (usize, usize)
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
        result.0 > 0,
        result.1 > 0,
        result.0 * result.1 == arr.len(),
{
    let r = if shape[0] == 0 {
        arr.len() / shape[1]
    } else {
        shape[0]
    };
    
    let c = if shape[1] == 0 {
        arr.len() / shape[0]
    } else {
        shape[1]
    };
    
    (r, c)
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
    /* code modified by LLM (iteration 5): No changes needed, implementation unchanged */
    let (rows, cols) = compute_dimensions(&arr, &shape);
    
    let mut result: Matrix<i32> = Vec::new();
    let mut idx: usize = 0;
    
    let mut i: usize = 0;
    while i < rows
        invariant
            rows > 0,
            cols > 0,
            rows * cols == arr.len(),
            0 <= idx <= arr.len(),
            idx == i * cols,
            result.len() == i,
            i <= rows,
            forall|row_idx: int| 0 <= row_idx < i ==> #[trigger] result[row_idx].len() == cols,
            forall|k: nat| k < idx ==> #[trigger] get_vector_element(arr@, k) == result[((k as usize) / cols) as int][((k as usize) % cols) as int],
        decreases rows - i
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        
        while j < cols
            invariant
                rows > 0,
                cols > 0,
                rows * cols == arr.len(),
                i < rows,
                0 <= idx <= arr.len(),
                idx == i * cols + j,
                j <= cols,
                row.len() == j,
                result.len() == i,
                forall|row_idx: int| 0 <= row_idx < i ==> #[trigger] result[row_idx].len() == cols,
                forall|k: nat| k < i * cols ==> #[trigger] get_vector_element(arr@, k) == result[((k as usize) / cols) as int][((k as usize) % cols) as int],
                forall|k: nat| i * cols <= k && k < idx ==> #[trigger] get_vector_element(arr@, k) == row[((k as usize) % cols) as int],
            decreases cols - j
        {
            assert(idx < arr.len());
            row.push(arr[idx]);
            idx = idx + 1;
            j = j + 1;
        }
        
        assert(row.len() == cols);
        result.push(row);
        i = i + 1;
    }
    
    assert(result.len() == rows);
    assert(forall|row_idx: int| 0 <= row_idx < rows ==> result[row_idx].len() == cols);
    assert(idx == arr.len());
    
    result
}
// </vc-code>


}
fn main() {}