use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
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
        let mut sum = 0;
        // Cofactor expansion along first row
        let mut j = 0;
        while j < n {
            let sign = if j % 2 == 0 { 1 } else { -1 };
            let minor = get_minor(matrix, 0, j, n);
            sum = sum + sign * matrix[0][j] * determinant_spec(minor, n - 1);
            j = j + 1;
        }
        sum
    }
}

// Helper function to get minor matrix (removing row i and column j)
spec fn get_minor(matrix: Seq<Seq<int>>, row_to_remove: int, col_to_remove: int, n: int) -> Seq<Seq<int>> {
    let mut minor: Seq<Seq<int>> = Seq::empty();
    let mut i = 0;
    while i < n {
        if i != row_to_remove {
            let mut new_row: Seq<int> = Seq::empty();
            let mut j = 0;
            while j < n {
                if j != col_to_remove {
                    new_row = new_row.push(matrix[i][j]);
                }
                j = j + 1;
            }
            minor = minor.push(new_row);
        }
        i = i + 1;
    }
    minor
}

fn Determinant(X: &Vec<Vec<i32>>, M: usize) -> (z: i32)
    requires
        M >= 1,
        X.len() == M,
        forall|i: usize| i < M ==> #[trigger] X[i].len() == M,
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
            {
                let mut new_row: Vec<i32> = Vec::new();
                let mut k: usize = 0;
                
                while k < M
                    invariant
                        k <= M,
                        new_row.len() == if k <= j { k } else { k - 1 },
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
            let minor_det = if M == 2 {
                1 // This case is handled above, but needed for the recursive structure
            } else {
                Determinant(&minor, M - 1)
            };
            
            result += sign * X[0][j] * minor_det;
            j += 1;
        }
        
        result
    }
}

}