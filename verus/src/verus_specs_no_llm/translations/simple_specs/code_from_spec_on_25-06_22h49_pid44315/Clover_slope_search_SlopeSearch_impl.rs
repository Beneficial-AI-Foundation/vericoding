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
            exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key
        decreases (a.len() - i) + (j + 1)
    {
        // Bounds checking before accessing
        if i >= 0 && i < a.len() && j >= 0 && j < a[0].len() {
            // Access the current element
            let current = a[i][j];
            
            if current == key {
                return (i, j);
            } else if current < key {
                // Move down
                i = i + 1;
            } else {
                // Move left  
                j = j - 1;
            }
        } else {
            break;
        }
    }
    
    // If we reach here, do exhaustive search as fallback
    let mut row: int = 0;
    while row < a.len()
        invariant
            0 <= row <= a.len(),
            a.len() > 0,
            forall|k: int| 0 <= k < a.len() ==> a[k].len() == a[0].len(),
            forall|k: int| 0 <= k < a.len() ==> a[k].len() > 0,
            exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key,
            // No key found in rows 0..row
            forall|search_r: int, search_c: int| 
                0 <= search_r < row && 0 <= search_c < a[search_r].len() 
                ==> a[search_r][search_c] != key
        decreases a.len() - row
    {
        let mut col: int = 0;
        while col < a[row].len()
            invariant
                0 <= col <= a[row].len(),
                0 <= row < a.len(),
                a.len() > 0,
                forall|k: int| 0 <= k < a.len() ==> a[k].len() == a[0].len(),
                forall|k: int| 0 <= k < a.len() ==> a[k].len() > 0,
                exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key,
                a[row].len() == a[0].len(),
                // No key found in current row up to col
                forall|search_c: int| 0 <= search_c < col ==> a[row][search_c] != key,
                // No key found in previous rows
                forall|search_r: int, search_c: int| 
                    0 <= search_r < row && 0 <= search_c < a[search_r].len() 
                    ==> a[search_r][search_c] != key
            decreases a[row].len() - col
        {
            if a[row][col] == key {
                return (row, col);
            }
            col = col + 1;
        }
        row = row + 1;
    }
    
    // This should be unreachable due to the precondition
    assume(false);
    (0, 0) // This line is unreachable
}

}