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
        // Cofactor expansion along first row using recursion instead of loops
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
        // For larger matrices, use cofactor expansion along first row
        let mut result: i32 = 0;
        let mut j: usize = 0;
        
        while j < M
            invariant
                j <= M,
                M >= 1,
                X.len() == M,
                forall|i: usize| i < M ==> #[trigger] X[i].len() == M,
                result == determinant_cofactor_sum_exec(vec_to_seq(*X), M as int, 0, j as int),
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
                
                proof {
                    assert(new_row.len() == M - 1);
                }
                minor.push(new_row);
                i += 1;
            }
            
            proof {
                assert(minor.len() == M - 1);
                assert(forall|idx: usize| idx < minor.len() ==> minor[idx].len() == M - 1);
            }
            
            // Recursively calculate determinant of minor
            let minor_det = Determinant(&minor, M - 1);
            
            result = result + sign * X[0][j] * minor_det;
            j += 1;
        }
        
        proof {
            assert(result == determinant_cofactor_sum_exec(vec_to_seq(*X), M as int, 0, M as int));
            assert(determinant_cofactor_sum_exec(vec_to_seq(*X), M as int, 0, M as int) == 
                   determinant_cofactor_sum(vec_to_seq(*X), M as int, 0));
        }
        
        result
    }
}

// Helper spec function to track partial sums during execution
spec fn determinant_cofactor_sum_exec(matrix: Seq<Seq<int>>, n: int, start: int, current: int) -> int
    decreases n, n - start, current - start
{
    if start >= current || current > n {
        0
    } else {
        determinant_cofactor_sum_range(matrix, n, start, current)
    }
}

spec fn determinant_cofactor_sum_range(matrix: Seq<Seq<int>>, n: int, start: int, end: int) -> int
    decreases n, n - start, end - start
{
    if start >= end {
        0
    } else {
        let sign = if start % 2 == 0 { 1 } else { -1 };
        let minor = get_minor(matrix, 0, start, n);
        let cofactor = sign * matrix[0][start] * determinant_spec(minor, n - 1);
        cofactor + determinant_cofactor_sum_range(matrix, n, start + 1, end)
    }
}

}