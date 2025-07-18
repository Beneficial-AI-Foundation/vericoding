use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to check if coordinates are valid
spec fn valid_coords(rows: int, cols: int, i: int, j: int) -> bool {
    0 <= i < rows && 0 <= j < cols
}

fn SlopeSearch(a: Seq<Seq<int>>, key: int) -> (m: int, n: int)
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i].len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i].len() == a[0].len(), // All rows same length
        forall|i: int, j: int, j_prime: int| 
            0 <= i < a.len() && 0 <= j < j_prime < a[i].len() 
            ==> a[i][j] <= a[i][j_prime], // Non-decreasing in rows
        forall|i: int, i_prime: int, j: int| 
            0 <= i < i_prime < a.len() && 0 <= j < a[i].len() 
            ==> a[i][j] <= a[i_prime][j], // Non-decreasing in columns
        exists|i: int, j: int| 
            0 <= i < a.len() && 0 <= j < a[i].len() && a[i][j] == key
    ensures
        0 <= m < a.len() && 0 <= n < a[m].len(),
        a[m][n] == key
{
    // Start from top-right corner
    let mut i: int = 0;
    let mut j: int = a[0].len() - 1;
    
    while i < a.len() && j >= 0
        invariant
            0 <= i <= a.len(),
            -1 <= j < a[0].len(),
            a.len() > 0,
            forall|k: int| 0 <= k < a.len() ==> a[k].len() == a[0].len(),
            forall|k: int| 0 <= k < a.len() ==> a[k].len() > 0,
            // Matrix properties preserved
            forall|row: int, col1: int, col2: int| 
                0 <= row < a.len() && 0 <= col1 < col2 < a[row].len() 
                ==> a[row][col1] <= a[row][col2],
            forall|row1: int, row2: int, col: int| 
                0 <= row1 < row2 < a.len() && 0 <= col < a[row1].len() 
                ==> a[row1][col] <= a[row2][col],
            // Key still exists
            exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key,
            // Search space constraints
            forall|r: int, c: int| (0 <= r < i && 0 <= c < a[0].len()) ==> a[r][c] < key,
            forall|r: int, c: int| (0 <= r < a.len() && j < c < a[0].len()) ==> a[r][c] > key
        decreases a.len() - i + j + 1
    {
        // Check bounds before accessing
        if i >= a.len() || j < 0 {
            break;
        }
        
        // Access the current element
        let current = a[i as nat][j as nat];
        
        if current == key {
            return (i, j);
        } else if current < key {
            // Move down
            i = i + 1;
        } else {
            // Move left  
            j = j - 1;
        }
    }
    
    // If we reach here, do exhaustive search as fallback
    // This should not happen given the precondition, but we need it for verification
    let mut row: int = 0;
    while row < a.len()
        invariant
            0 <= row <= a.len(),
            a.len() > 0,
            forall|k: int| 0 <= k < a.len() ==> a[k].len() == a[0].len(),
            forall|k: int| 0 <= k < a.len() ==> a[k].len() > 0,
            exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key,
            forall|r: int, c: int| 0 <= r < row && 0 <= c < a[r].len() ==> a[r][c] != key
        decreases a.len() - row
    {
        let mut col: int = 0;
        while col < a[row as nat].len()
            invariant
                0 <= col <= a[row as nat].len(),
                0 <= row < a.len(),
                a.len() > 0,
                forall|k: int| 0 <= k < a.len() ==> a[k].len() == a[0].len(),
                forall|k: int| 0 <= k < a.len() ==> a[k].len() > 0,
                exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key,
                forall|c_prev: int| 0 <= c_prev < col ==> a[row as nat][c_prev as nat] != key,
                forall|r_prev: int, c_any: int| 0 <= r_prev < row && 0 <= c_any < a[r_prev].len() ==> a[r_prev][c_any] != key
            decreases a[row as nat].len() - col
        {
            if a[row as nat][col as nat] == key {
                return (row, col);
            }
            col = col + 1;
        }
        row = row + 1;
    }
    
    // This should be unreachable due to the precondition
    proof {
        // We've searched the entire matrix and didn't find the key
        assert(forall|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() ==> a[r][c] != key);
        // But the precondition guarantees the key exists
        assert(exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key);
        // This is a contradiction
        assert(false);
    }
    
    (0, 0) // This line is unreachable
}

}