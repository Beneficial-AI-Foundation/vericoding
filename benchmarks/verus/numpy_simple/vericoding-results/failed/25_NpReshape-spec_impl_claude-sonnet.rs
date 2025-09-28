// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemmas for proper postcondition proofs */
spec fn valid_matrix_index<T>(mat: Matrix<T>, row: int, col: int) -> bool {
    0 <= row < mat.len() && mat.len() > 0 && 0 <= col < mat[row as int].len()
}

spec fn arr_index_in_bounds(arr_len: nat, index: nat) -> bool {
    index < arr_len
}

spec fn compute_rows(shape0: usize, shape1: usize, arr_len: usize) -> usize {
    if shape0 > 0 { shape0 } else { arr_len / shape1 }
}

spec fn compute_cols(shape0: usize, shape1: usize, arr_len: usize) -> usize {
    if shape1 > 0 { shape1 } else { arr_len / shape0 }
}

proof fn lemma_matrix_size_correct(result: Matrix<i32>, rows: usize, cols: usize)
    requires
        result.len() == rows,
        rows > 0,
        cols > 0,
        forall|r: int| 0 <= r < rows ==> result[r].len() == cols,
    ensures
        matrix_size(result) == (rows * cols) as nat,
{
    assert(matrix_size(result) == (result.len() * result[0].len()) as nat);
    assert(result.len() == rows);
    assert(result[0].len() == cols);
}

proof fn lemma_index_bounds(i: nat, rows: usize, cols: usize, arr_len: usize)
    requires
        i < arr_len,
        rows > 0,
        cols > 0,
        rows * cols == arr_len,
    ensures
        (i as usize) / cols < rows,
        (i as usize) % cols < cols,
{
    let row_idx = (i as usize) / cols;
    let col_idx = (i as usize) % cols;
    assert(i < arr_len);
    assert(arr_len == rows * cols);
    assert(row_idx < rows);
    assert(col_idx < cols);
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
    /* code modified by LLM (iteration 5): added proper postcondition proofs with lemmas */
    let rows = if shape[0] > 0 { shape[0] } else { arr.len() / shape[1] };
    let cols = if shape[1] > 0 { shape[1] } else { arr.len() / shape[0] };
    
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0;
    
    proof {
        if shape[0] > 0 && shape[1] > 0 {
            assert(rows == shape[0] && cols == shape[1]);
            assert(shape[0] * shape[1] == arr.len());
            assert(rows * cols == arr.len());
        } else if shape[0] == 0 {
            assert(arr.len() % shape[1] == 0);
            assert(rows == arr.len() / shape[1] && cols == shape[1]);
            assert(rows * cols == arr.len());
        } else {
            assert(arr.len() % shape[0] == 0);
            assert(rows == shape[0] && cols == arr.len() / shape[0]);
            assert(rows * cols == arr.len());
        }
        assert(rows > 0);
        assert(cols > 0);
    }
    
    while i < rows
        invariant
            i <= rows,
            result.len() == i,
            rows > 0,
            cols > 0,
            rows * cols == arr.len(),
            forall|r: int| 0 <= r < i ==> #[trigger] result[r].len() == cols,
            forall|r: int, c: int| 0 <= r < i && 0 <= c < cols ==> 
                0 <= r * cols + c < arr.len() &&
                #[trigger] result[r][c] == arr[(r * cols + c) as int],
        decreases rows - i
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j = 0;
        
        while j < cols
            invariant
                j <= cols,
                row.len() == j,
                cols > 0,
                i < rows,
                rows * cols == arr.len(),
                i * cols + j <= rows * cols,
                forall|c: int| 0 <= c < j ==> 
                    0 <= i * cols + c < arr.len() &&
                    #[trigger] row[c] == arr[(i * cols + c) as int],
            decreases cols - j
        {
            proof {
                assert(i < rows);
                assert(j < cols);
                assert(i * cols + j < i * cols + cols);
                assert(i * cols + cols <= rows * cols);
                assert(rows * cols == arr.len());
                assert(i * cols + j < arr.len());
            }
            row.push(arr[(i * cols + j) as usize]);
            j += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    proof {
        lemma_matrix_size_correct(result, rows, cols);
        
        assert forall|idx: nat| idx < arr.len() implies {
            lemma_index_bounds(idx, rows, cols, arr.len());
            let row_idx = (idx as usize) / cols;
            let col_idx = (idx as usize) % cols;
            assert(0 <= row_idx < result.len());
            assert(0 <= col_idx < result[row_idx as int].len());
            assert(result[row_idx as int][col_idx as int] == arr[idx as int]);
        } by {
            let idx = idx;
            lemma_index_bounds(idx, rows, cols, arr.len());
            let row_idx = (idx as usize) / cols;
            let col_idx = (idx as usize) % cols;
            assert(idx == (row_idx * cols + col_idx) as nat);
        };
    }
    
    result
}
// </vc-code>


}
fn main() {}