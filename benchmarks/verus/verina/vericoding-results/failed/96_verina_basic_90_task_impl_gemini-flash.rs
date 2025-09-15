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
/* helper modified by LLM (iteration 5): Removed helper function due to complexity and ineffectiveness. */
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
/* code modified by LLM (iteration 5): Fixed `forall` clause in `invariant` by removing extraneous comma. */
{
    let rows: usize = a.len();
    let cols: usize = a[0].len();

    if rows == 0 || cols == 0 {
        return (-1, -1);
    }

    let mut r: usize = 0;
    let mut c: usize = cols - 1;

    while r < rows && (c as int) >= 0
        invariant
            0 <= r as int,
            r <= rows,
            (c as int) >= -1,
            c < cols,
            forall|i: int, j: int| 0 <= i < r as int && 0 <= j < cols as int ==> #[trigger] a[i as usize][j as usize] != key,
            forall|i: int, j: int| r as int <= i && i < rows as int && c as int < j && j < cols as int ==> #[trigger] a[i as usize][j as usize] != key,
    {
        if a[r][c] == key {
            return (r as i32, c as i32);
        } else if a[r][c] < key {
            r = r + 1;
        } else { // a[r][c] > key
            c = c - 1;
        }
    }

    (-1, -1)
}
// </vc-code>

}
fn main() {}