// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn slope_search_precond(a: &Vec<Vec<i32>>, key: i32) -> bool {
    a.len() > 0 &&
    (forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == a[0].len()) &&
    (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i].len() - 1 ==> #[trigger] a[i][j] <= a[i][j + 1]) &&
    (forall|j: int, i: int| 0 <= j < a[0].len() && 0 <= i < a.len() - 1 ==> #[trigger] a[i][j] <= a[i + 1][j])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn slope_search(a: &Vec<Vec<i32>>, key: i32) -> (result: (i32, i32))
    requires slope_search_precond(a, key),
    ensures
        ({
            let (m, n) = result;
            ((m >= 0 && m < a.len() && n >= 0 && n < a[0].len() && a[m as int][n as int] == key) ||
             (m == -1 && n == -1 && forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i].len() ==> #[trigger] a[i][j] != key))
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added missing outer braces and fixed syntax */
    // Check for empty columns
    if a[0].len() == 0 {
        return (-1, -1);
    }

    let m = a.len() as isize;
    let n = a[0].len() as isize;
    let mut row: isize = 0;
    let mut col: isize = n - 1;

    while row < m && col >= 0
        invariant 
            0 <= row <= m,
            -1 <= col < n,
            forall|i: int, j: int| 0<=i<m && 0<=j<n && i < row ==> a[i][j] != key,
            forall|i: int, j: int| 0<=i<m && 0<=j<n && j > col ==> a[i][j] != key,
        decreases (m - row) + col
    {
        // Assert bounds for indexing
        assert(0 <= row < m);
        assert(0 <= col < n);

        if a[row as usize][col as usize] == key {
            return (row as i32, col as i32);
        } else if a[row as usize][col as usize] > key {
            col -= 1;
        } else {
            row += 1;
        }
    }

    return (-1, -1);
}
// </vc-code>

}
fn main() {}