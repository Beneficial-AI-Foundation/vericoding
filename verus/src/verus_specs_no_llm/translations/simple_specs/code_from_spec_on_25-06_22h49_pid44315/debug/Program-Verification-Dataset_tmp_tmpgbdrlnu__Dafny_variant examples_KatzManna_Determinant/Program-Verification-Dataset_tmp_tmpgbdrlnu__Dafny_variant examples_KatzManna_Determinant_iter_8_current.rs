use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper function to convert Vec<Vec<i32>> to Seq<Seq<int>>
spec fn vec_to_seq(v: Vec<Vec<i32>>) -> Seq<Seq<int>> {
    Seq::new(v.len() as int, |i: int| {
        Seq::new(v[i as usize].len() as int, |j: int| v[i as usize][j as usize] as int)
    })
}

// Helper function to get minor matrix (removing row i and column j)
spec fn get_minor(matrix: Seq<Seq<int>>, row_to_remove: int, col_to_remove: int, n: int) -> Seq<Seq<int>> {
    Seq::new(n - 1, |i: int| {
        let actual_row = if i < row_to_remove { i } else { i + 1 };
        Seq::new(n - 1, |j: int| {
            let actual_col = if j < col_to_remove { j } else { j + 1 };
            matrix[actual_row][actual_col]
        })
    })
}

// Helper function to calculate determinant recursively
spec fn determinant_spec(matrix: Seq<Seq<int>>, n: int) -> int
    decreases n
{
    if n == 1 {
        matrix[0][0]
    } else if n == 2 {
        matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
    } else {
        determinant_cofactor_sum(matrix, n, 0)
    }
}

// Helper spec function to calculate cofactor sum recursively
spec fn determinant_cofactor_sum(matrix: Seq<Seq<int>>, n: int, j: int) -> int
    decreases n, n - j
{
    if j >= n {
        0
    } else {
        let sign = if j % 2 == 0 { 1 } else { -1 };
        let minor = get_minor(matrix, 0, j, n);
        let cofactor = sign * matrix[0][j] * determinant_spec(minor, n - 1);
        cofactor + determinant_cofactor_sum(matrix, n, j + 1)
    }
}

// Helper spec function to track partial sums during execution
spec fn determinant_cofactor_sum_partial(matrix: Seq<Seq<int>>, n: int, current_j: int) -> int
    decreases n, n - current_j
{
    if current_j >= n {
        0
    } else {
        let sign = if current_j % 2 == 0 { 1 } else { -1 };
        let minor = get_minor(matrix, 0, current_j, n);
        let cofactor = sign * matrix[0][current_j] * determinant_spec(minor, n - 1);
        cofactor + determinant_cofactor_sum_partial(matrix, n, current_j + 1)
    }
}

// Lemma to prove equivalence between cofactor sum functions
proof fn lemma_cofactor_sum_equiv(matrix: Seq<Seq<int>>, n: int, j: int)
    ensures determinant_cofactor_sum(matrix, n, j) == determinant_cofactor_sum_partial(matrix, n, j)
    decreases n, n - j
{
    if j >= n {
        // Base case: both return 0
    } else {
        // Recursive case
        lemma_cofactor_sum_equiv(matrix, n, j + 1);
    }
}

// Helper spec function to convert minor matrix representation
spec fn minor_vec_to_seq(original: Seq<Seq<int>>, row_skip: int, col_skip: int, n: int) -> Seq<Seq<int>>
{
    get_minor(original, row_skip, col_skip, n)
}

fn Determinant(X: &Vec<Vec<i32>>, M: usize) -> (z: i32)
    requires
        M >= 1,
        X.len() == M,
        forall|i: usize| i < M ==> #[trigger] X[i].len() == M,
    ensures
        z == determinant_spec(vec_to_seq(*X), M as int),
    decreases M
{
    if M == 1 {
        X[0][0]
    } else if M == 2 {
        X[0][0] * X[1][1] - X[0][1] * X[1][0]
    } else {
        let mut result: i32 = 0;
        let mut j: usize = 0;
        
        while j < M
            invariant
                j <= M,
                M >= 1,
                X.len() == M,
                forall|i: usize| i < M ==> #[trigger] X[i].len() == M,
                result == (determinant_cofactor_sum(vec_to_seq(*X), M as int, 0) - 
                          determinant_cofactor_sum_partial(vec_to_seq(*X), M as int, j as int)),
        {
            let sign = if j % 2 == 0 { 1 } else { -1 };
            
            // Create minor matrix (removing row 0 and column j)
            let mut minor: Vec<Vec<i32>> = Vec::new();
            let mut i: usize = 1;
            
            while i < M
                invariant
                    i >= 1,
                    i <= M,
                    minor.len() == (i - 1),
                    M >= 1,
                    j < M,
                    X.len() == M,
                    forall|row_idx: usize| row_idx < M ==> #[trigger] X[row_idx].len() == M,
                    forall|k: usize| k < minor.len() ==> #[trigger] minor[k].len() == M - 1,
            {
                let mut new_row: Vec<i32> = Vec::new();
                let mut k: usize = 0;
                
                while k < M
                    invariant
                        k <= M,
                        M >= 1,
                        i < M,
                        j < M,
                        X.len() == M,
                        forall|row_idx: usize| row_idx < M ==> #[trigger] X[row_idx].len() == M,
                        new_row.len() <= M - 1,
                        k >= j ==> new_row.len() == k - 1,
                        k < j ==> new_row.len() == k,
                {
                    if k != j {
                        new_row.push(X[i][k]);
                    }
                    k += 1;
                }
                
                minor.push(new_row);
                i += 1;
            }
            
            // Recursively calculate determinant of minor
            let minor_det = Determinant(&minor, M - 1);
            
            let old_result = result;
            result = result + sign * X[0][j] * minor_det;
            
            proof {
                lemma_cofactor_sum_equiv(vec_to_seq(*X), M as int, (j + 1) as int);
            }
            
            j += 1;
        }
        
        proof {
            assert(j == M);
            assert(determinant_cofactor_sum_partial(vec_to_seq(*X), M as int, M as int) == 0);
            lemma_cofactor_sum_equiv(vec_to_seq(*X), M as int, 0);
        }
        
        result
    }
}

}