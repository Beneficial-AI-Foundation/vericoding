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
            forall|k: int| 0 <= k < a.len() ==> a[k].len() > 0,
            // Elements in eliminated regions
            forall|r: int, c: int| (0 <= r < i && 0 <= c < a[0].len()) ==> a[r][c] < key,
            forall|r: int, c: int| (0 <= r < a.len() && j < c < a[0].len()) ==> a[r][c] > key,
            // Key still exists somewhere
            exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key,
            // Matrix properties preserved
            forall|row: int, col1: int, col2: int| 
                0 <= row < a.len() && 0 <= col1 < col2 < a[row].len() 
                ==> a[row][col1] <= a[row][col2],
            forall|row1: int, row2: int, col: int| 
                0 <= row1 < row2 < a.len() && 0 <= col < a[row1].len() 
                ==> a[row1][col] <= a[row2][col]
        decreases a.len() - i + j + 1
    {
        // Check bounds before accessing array
        if i < a.len() && j >= 0 {
            // Ensure j is within bounds for current row
            assert(a[i].len() == a[0].len());
            if j < a[i].len() {
                if a[i][j] == key {
                    return (i, j);
                } else if a[i][j] < key {
                    // All elements to the left in this row are also < key
                    assert(forall|c: int| 0 <= c <= j ==> a[i][c] <= a[i][j]);
                    assert(forall|c: int| 0 <= c <= j ==> a[i][c] < key);
                    i = i + 1;
                } else {
                    // a[i][j] > key, all elements below in this column are also > key
                    assert(forall|r: int| i <= r < a.len() ==> a[i][j] <= a[r][j]);
                    assert(forall|r: int| i <= r < a.len() ==> a[r][j] > key);
                    j = j - 1;
                }
            } else {
                // j >= a[i].len(), which means j >= a[0].len(), so move to next row
                i = i + 1;
            }
        } else {
            break;
        }
    }
    
    // If we reach here, search exhaustively in the remaining space
    let mut row: int = 0;
    while row < a.len()
        invariant
            0 <= row <= a.len(),
            a.len() > 0,
            forall|k: int| 0 <= k < a.len() ==> a[k].len() == a[0].len(),
            forall|k: int| 0 <= k < a.len() ==> a[k].len() > 0,
            exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key,
            // We haven't found the key in rows 0..row
            forall|r: int, c: int| 0 <= r < row && 0 <= c < a[r].len() ==> a[r][c] != key
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
                // We haven't found the key in columns 0..col of current row
                forall|c_prev: int| 0 <= c_prev < col ==> a[row][c_prev] != key,
                // We haven't found the key in previous rows
                forall|r: int, c_any: int| 0 <= r < row && 0 <= c_any < a[r].len() ==> a[r][c_any] != key
            decreases a[row].len() - col
        {
            if a[row][col] == key {
                return (row, col);
            }
            col = col + 1;
        }
        
        // Assert that we've checked all positions in this row
        assert(forall|c: int| 0 <= c < a[row].len() ==> a[row][c] != key);
        row = row + 1;
    }
    
    // This should be unreachable due to the precondition guaranteeing key exists
    proof {
        // We've exhaustively searched all positions
        assert(forall|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() ==> a[r][c] != key);
        // But precondition says key exists
        assert(exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key);
        // This is a contradiction
        assert(false);
    }
    
    // Unreachable, but needed for compilation
    (0, 0)
}

}