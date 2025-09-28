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
/* helper modified by LLM (iteration 5): nested loops linear search with bounds and invariants */
fn linear_search(a: &Vec<Vec<i32>>, key: i32, rows: usize, cols: usize) -> (i32, i32)
    requires
        rows == a.len(),
        cols == a[0].len(),
        (forall|i: int| 0 <= i < a.len() ==> a[i].len() == a[0].len())
{
    let mut r: usize = 0;
    while r < rows
        invariant
            r <= rows,
        decreases rows - r
    {
        let mut c: usize = 0;
        while c < cols
            invariant
                r <= rows,
                c <= cols,
            decreases cols - c
        {
            if a[r][c] == key {
                return (r as i32, c as i32);
            }
            c += 1;
        }
        r += 1;
    }
    (-1, -1)
}
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
    /* code modified by LLM (iteration 5): call linear_search with verified rows and cols */
    let rows = a.len();
    let cols = a[0].len();
    linear_search(a, key, rows, cols)
}
// </vc-code>

}
fn main() {}