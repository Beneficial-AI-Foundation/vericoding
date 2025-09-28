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
/* helper modified by LLM (iteration 5): no helpers needed */
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
/* code modified by LLM (iteration 5): corrected while loop syntax and invariants for compilation */
{
    let mut row: usize = 0;
    let mut col: i32 = (a[0].len() - 1) as i32;
    while row < a.len() && col >= 0
        invariant
            0 <= row && row <= a.len(),
            -1 <= col && col < (a[0].len() as i32),
            forall |i: int, j: int|
                (0 <= i < (row as int) && 0 <= j < a[0].len()) || (0 <= i < a.len() && 0 <= j <= (col as int))
                ==> #[trigger] (a[i][j] != key),
        decreases a.len() - row + (if col >= 0 { col as usize } else { 0 })
    {
        if a[row][col as usize] == key {
            return (row as i32, col);
        } else if a[row][col as usize] > key {
            col -= 1;
        } else {
            row += 1;
        }
    }
    (-1, -1)
}
// </vc-code>

}
fn main() {}