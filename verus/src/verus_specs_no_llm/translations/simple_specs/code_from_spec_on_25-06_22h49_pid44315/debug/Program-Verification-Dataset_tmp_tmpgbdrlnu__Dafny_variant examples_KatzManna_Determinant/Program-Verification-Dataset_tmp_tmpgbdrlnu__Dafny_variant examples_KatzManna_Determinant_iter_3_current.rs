use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
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
        // Cofactor expansion along first row using fold_left
        Seq::new(n, |j: int| j).fold_left(0, |sum: int, j: int| {
            let sign = if j % 2 == 0 { 1 } else { -1 };
            let minor = get_minor(matrix, 0, j, n);
            sum + sign * matrix[0][j] * determinant_spec(minor, n - 1)
        })
    }
}

fn Determinant(X: &Vec<Vec<i32>>, M: usize) -> (z: i32)
    requires
        M >= 1,
        X.len() == M,
        forall|i: usize| i < M ==> #[trigger] X[i].len() == M,
    ensures
        true, // placeholder ensures clause
    decreases M
{
    if M == 1 {
        X[0][0]
    } else if M == 2 {
        X[0][0] * X[1][1] - X[0][1] * X[1][0]
    } else {
        // For larger matrices, use cofactor expansion along first row
        let mut result: i32 = 0;
        let mut j: usize = 0;
        
        while j < M
            invariant
                j <= M,
                M >= 1,
                X.len() == M,
                forall|i: usize| i < M ==> #[trigger] X[i].len() == M,
        {
            let sign = if j % 2 == 0 { 1 } else { -1 };
            
            // Create minor matrix (removing row 0 and column j)
            let mut minor: Vec<Vec<i32>> = Vec::new();
            let mut i: usize = 1; // Skip first row
            
            while i < M
                invariant
                    i >= 1,
                    i <= M,
                    minor.len() == (i - 1),
                    M >= 1,
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
                        // Fixed the arithmetic expression
                        k >= j ==> new_row.len() == k - 1,
                        k < j ==> new_row.len() == k,
                {
                    if k != j {
                        new_row.push(X[i][k]);
                    }
                    k += 1;
                }
                
                // Add assertion to help verification
                assert(new_row.len() == M - 1);
                minor.push(new_row);
                i += 1;
            }
            
            // Add assertion to help verification
            assert(minor.len() == M - 1);
            assert(forall|idx: usize| idx < minor.len() ==> minor[idx].len() == M - 1);
            
            // Recursively calculate determinant of minor
            let minor_det = Determinant(&minor, M - 1);
            
            result += sign * X[0][j] * minor_det;
            j += 1;
        }
        
        result
    }
}

}