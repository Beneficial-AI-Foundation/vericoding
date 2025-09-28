// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 4): Fixed nat usage in ghost code */
spec fn shape_dimensions_are_valid(shape: Vec<usize>) -> bool {
    shape.len() == 2 && (
        (shape[0] > 0 && shape[1] > 0) ||
        (shape[0] == 0 && shape[1] > 0) ||
        (shape[0] > 0 && shape[1] == 0)
    )
}

spec fn calculate_rows(shape: Vec<usize>, length: usize) -> usize {
    if shape[0] > 0 {
        shape[0]
    } else {
        length / shape[1]
    }
}

spec fn calculate_cols(shape: Vec<usize>, length: usize) -> usize {
    if shape[1] > 0 {
        shape[1]
    } else {
        length / shape[0]
    }
}

proof fn matrix_elements_preserved(arr: Seq<i32>, mat: Matrix<i32>, rows: usize, cols: usize)
    requires
        rows > 0,
        cols > 0,
        rows * cols == arr.len(),
    ensures
        forall|i: nat| i < arr.len() ==> #[trigger] arr[i] == mat[(i / cols as nat) as int][(i % cols as nat) as int]
{
    assert_forall_by(|i: nat| {
        requires(i < arr.len());
        ensures(arr[i] == mat[(i / cols as nat) as int][(i % cols as nat) as int]);
        
        let row = (i / cols as nat) as int;
        let col = (i % cols as nat) as int;
        assert(row >= 0 && row < rows as int);
        assert(col >= 0 && col < cols as int);
    });
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
    /* code modified by LLM (iteration 4): Fixed int/nat casting for exec mode */
    let total_elements = arr.len();
    let rows: usize;
    let cols: usize;
    
    proof {
        assert(shape.len() == 2);
        assert(shape_dimensions_are_valid(shape));
        assert_by(if shape[0] > 0 && shape[1] > 0 {
            shape[0] * shape[1] == total_elements
        } else if shape[0] == 0 {
            total_elements % shape[1] == 0
        } else {
            total_elements % shape[0] == 0
        },);
    }
    
    if shape[0] > 0 && shape[1] > 0 {
        rows = shape[0];
        cols = shape[1];
    } else if shape[0] == 0 {
        rows = total_elements / shape[1];
        cols = shape[1];
    } else {
        rows = shape[0];
        cols = total_elements / shape[0];
    }
    
    proof {
        let r = calculate_rows(shape, total_elements);
        let c = calculate_cols(shape, total_elements);
        assert(rows == r && cols == c);
        assert(r > 0 && c > 0);
        assert(r * c == total_elements);
    }
    
    let mut result: Matrix<i32> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < total_elements
        invariant
            idx <= total_elements,
            result.len() == idx / cols,
            forall|r: int| 0 <= r < result.len() ==> result[r].len() == cols,
            forall|i: nat| i < idx ==> #[trigger] result@[(i / cols as nat) as int][(i % cols as nat) as int] == arr[i]
    {
        if idx % cols == 0 {
            let mut row_vec: Vec<i32> = Vec::new();
            result.push(row_vec);
        }
        
        let val = arr[idx];
        result[idx / cols].push(val);
        idx = idx + 1;
    }
    
    proof {
        matrix_elements_preserved(arr@, result, rows, cols);
    }
    
    result
}
// </vc-code>


}
fn main() {}