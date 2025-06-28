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

// Helper spec function to calculate partial sum up to index j
spec fn determinant_partial_sum(matrix: Seq<Seq<int>>, n: int, j: int) -> int
    decreases n, j
{
    if j <= 0 {
        0
    } else {
        let sign = if (j - 1) % 2 == 0 { 1 } else { -1 };
        let minor = get_minor(matrix, 0, j - 1, n);
        let cofactor = sign * matrix[0][j - 1] * determinant_spec(minor, n - 1);
        determinant_partial_sum(matrix, n, j - 1) + cofactor
    }
}

// Lemma relating partial sum to cofactor sum
proof fn lemma_partial_sum_relation(matrix: Seq<Seq<int>>, n: int, j: int)
    requires n >= 1, j >= 0, j <= n,
    ensures determinant_partial_sum(matrix, n, j) == 
            determinant_cofactor_sum(matrix, n, 0) - determinant_cofactor_sum(matrix, n, j),
    decreases n, j
{
    if j == 0 {
        // Base case: partial_sum(0) = 0, cofactor_sum(0) - cofactor_sum(0) = 0
    } else if j == n {
        // When j == n, cofactor_sum(n) = 0, so partial_sum(n) = cofactor_sum(0)
        lemma_partial_sum_relation(matrix, n, j - 1);
    } else {
        // Inductive case
        lemma_partial_sum_relation(matrix, n, j - 1);
    }
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
                result == determinant_partial_sum(spec_matrix, M as int, j as int),
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
                        new_row.len() == (if k <= j { k } else { k - 1 }),
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
            
            // Update result
            let cofactor = sign * X[0][j] * minor_det;
            result = result + cofactor;
            
            j += 1;
        }
        
        proof {
            lemma_partial_sum_relation(spec_matrix, M as int, M as int);
            assert(determinant_partial_sum(spec_matrix, M as int, M as int) == 
                   determinant_cofactor_sum(spec_matrix, M as int, 0));
            assert(determinant_spec(spec_matrix, M as int) == determinant_cofactor_sum(spec_matrix, M as int, 0));
        }
        
        result
    }
}

}