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
/* code modified by LLM (iteration 5): fixed invariant for `c as int <= cols as int - 1` by updating to `c as int < cols as int` and removed `a[r as int][c as int] == key || a[r as int][c as int] != key` as it's redundant. Adjusted the loop condition to `(r < rows)` as `c < cols` is handled in the invariant. The invariant for cells already considered is updated to `a[row_idx][col_idx] != key` instead of `a[row_idx][col_idx] == key || a[row_idx][col_idx] != key` */
{
    let rows = a.len();
    let cols = a[0].len();

    if rows == 0 || cols == 0 {
        return (-1, -1);
    }

    let mut r: usize = 0;
    let mut c: usize = cols - 1; 

    while (r < rows)
        invariant
            0 <= r as int,
            r as int <= rows as int,
            0 <= c as int,
            c as int < cols as int,
            
            forall|row_idx: int, col_idx: int|
                0 <= row_idx && row_idx < rows as int && 0 <= col_idx && col_idx < cols as int &&
                (row_idx < r as int || col_idx > c as int)
                ==>
                a[row_idx][col_idx] != key
        decreases (rows as int - r as int) + (c as int + 1)
    {
        let current_val = a[r][c];

        if current_val == key {
            return (r as i32, c as i32);
        } else if current_val < key {
            r = r + 1;
        } else {
            if c == 0 {
                break;
            }
            c = c - 1;
        }
    }

    (-1, -1)
}
// </vc-code>

}
fn main() {}