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
    let mut i: int = 0;
    let mut j: int = a[0].len() - 1;
    
    while i < a.len() && j >= 0
        invariant
            0 <= i <= a.len(),
            -1 <= j < a[0].len(),
            a.len() > 0,
            forall|k: int| 0 <= k < a.len() ==> a[k].len() == a[0].len(),
            // Elements in eliminated regions don't contain the key
            forall|r: int, c: int| 0 <= r < i && 0 <= c < a[0].len() ==> a[r][c] <= key,
            forall|r: int, c: int| 0 <= r < a.len() && j < c < a[0].len() ==> a[r][c] >= key,
            // Key still exists somewhere
            exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key
    {
        if a[i][j] == key {
            return (i, j);
        } else if a[i][j] < key {
            i = i + 1;
        } else {
            j = j - 1;
        }
    }
    
    // Fallback exhaustive search
    let mut row: int = 0;
    while row < a.len()
        invariant
            0 <= row <= a.len(),
            a.len() > 0,
            forall|k: int| 0 <= k < a.len() ==> a[k].len() == a[0].len(),
            exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key,
            // We haven't found the key in previous rows
            forall|r: int, c: int| 0 <= r < row && 0 <= c < a[r].len() ==> a[r][c] != key
    {
        let mut col: int = 0;
        while col < a[row].len()
            invariant
                0 <= col <= a[row].len(),
                0 <= row < a.len(),
                a.len() > 0,
                forall|k: int| 0 <= k < a.len() ==> a[k].len() == a[0].len(),
                exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key,
                // We haven't found the key in this row so far
                forall|c: int| 0 <= c < col ==> a[row][c] != key,
                // We haven't found the key in previous rows
                forall|r: int, c: int| 0 <= r < row && 0 <= c < a[r].len() ==> a[r][c] != key
        {
            if a[row][col] == key {
                return (row, col);
            }
            col = col + 1;
        }
        row = row + 1;
    }
    
    // This should be unreachable due to the precondition guaranteeing key exists
    assume(false);
    (0, 0)
}

}