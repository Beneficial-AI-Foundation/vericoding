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
        if i < a.len() && j >= 0 && j < a[i].len() {
            if a[i as nat][j as nat] == key {
                return (i, j);
            } else if a[i as nat][j as nat] < key {
                i = i + 1;
            } else {
                j = j - 1;
            }
        } else {
            break;
        }
    }
    
    // Exhaustive search fallback
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
                forall|r: int, c_any: int| 0 <= r < row && 0 <= c_any < a[r].len() ==> a[r][c_any] != key
            decreases a[row as nat].len() - col
        {
            if a[row as nat][col as nat] == key {
                return (row, col);
            }
            col = col + 1;
        }
        row = row + 1;
    }
    
    // This point should be unreachable due to precondition
    proof {
        assert(forall|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() ==> a[r][c] != key);
        assert(exists|r: int, c: int| 0 <= r < a.len() && 0 <= c < a[r].len() && a[r][c] == key);
        assert(false);
    }
    
    (0, 0) // Unreachable
}

}