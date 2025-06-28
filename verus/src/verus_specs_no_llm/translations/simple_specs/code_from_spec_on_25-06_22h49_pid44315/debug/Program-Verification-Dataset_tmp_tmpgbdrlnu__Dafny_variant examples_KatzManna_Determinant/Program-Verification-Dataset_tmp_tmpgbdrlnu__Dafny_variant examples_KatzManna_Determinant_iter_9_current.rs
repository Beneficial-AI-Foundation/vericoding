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

// Lemma to prove cofactor sum decomposition
proof fn lemma_cofactor_decomposition(matrix: Seq<Seq<int>>, n: int, j: int)
    requires n >= 1, j < n,
    ensures 
        determinant_cofactor_sum(matrix, n, j) == 
        {
            let sign = if j % 2 == 0 { 1 } else { -1 };
            let minor = get_minor(matrix, 0, j, n);
            let cofactor = sign * matrix[0][j] * determinant_spec(minor, n - 1);
            cofactor + determinant_cofactor_sum(matrix, n, j + 1)
        }
    decreases n, n - j
{
    // Proof by definition unfolding
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
        let spec_matrix = vec_to_seq(*X);
        
        while j < M
            invariant
                j <= M,
                M >= 1,
                X.len() == M,
                forall|i: usize| i < M ==> #[trigger] X[i].len() == M,
                spec_matrix == vec_to_seq(*X),
                result == determinant_cofactor_sum(spec_matrix, M as int, 0) - 
                          determinant_cofactor_sum(spec_matrix, M as int, j as int),
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
                    forall|row: int, col: int| 
                        0 <= row < (i - 1) as int && 0 <= col < (M - 1) as int ==>
                        minor[row as usize][col as usize] as int == 
                        get_minor(spec_matrix, 0, j as int, M as int)[row][col],
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
                        new_row.len() == if k <= j { k } else { k - 1 },
                        forall|col: int| 
                            0 <= col < new_row.len() as int ==>
                            new_row[col as usize] as int == 
                            get_minor(spec_matrix, 0, j as int, M as int)[i as int - 1][col],
                {
                    if k != j {
                        new_row.push(X[i][k]);
                    }
                    k += 1;
                }
                
                minor.push(new_row);
                i += 1;
            }
            
            // Establish that minor represents the correct spec minor
            proof {
                let spec_minor = get_minor(spec_matrix, 0, j as int, M as int);
                assert(minor.len() == M - 1);
                assert(forall|row: int, col: int|
                    0 <= row < (M - 1) as int && 0 <= col < (M - 1) as int ==>
                    minor[row as usize][col as usize] as int == spec_minor[row][col]);
                assert(vec_to_seq(minor) =~= spec_minor);
            }
            
            // Recursively calculate determinant of minor
            let minor_det = Determinant(&minor, M - 1);
            
            // Update result
            let cofactor = sign * X[0][j] * minor_det;
            result = result + cofactor;
            
            proof {
                lemma_cofactor_decomposition(spec_matrix, M as int, j as int);
                // The cofactor we just added matches the spec
                let spec_sign = if j % 2 == 0 { 1 } else { -1 };
                let spec_minor = get_minor(spec_matrix, 0, j as int, M as int);
                let spec_cofactor = spec_sign * spec_matrix[0][j as int] * determinant_spec(spec_minor, M as int - 1);
                assert(cofactor == spec_cofactor);
            }
            
            j += 1;
        }
        
        proof {
            assert(j == M);
            assert(determinant_cofactor_sum(spec_matrix, M as int, M as int) == 0);
            assert(result == determinant_cofactor_sum(spec_matrix, M as int, 0));
            assert(determinant_spec(spec_matrix, M as int) == determinant_cofactor_sum(spec_matrix, M as int, 0));
        }
        
        result
    }
}

}