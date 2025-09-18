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
/* helper modified by LLM (iteration 5): Fixed function signature and return type */
fn check_bounds(i: i32, j: i32, rows: usize, cols: usize) -> bool
    ensures
        result == (i >= 0 && (i as usize) < rows && j >= 0 && (j as usize) < cols)
{
    i >= 0 && (i as usize) < rows && j >= 0 && (j as usize) < cols
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
    let rows = a.len();
    let cols = a[0].len();
    let mut i: i32 = 0;
    let mut j: i32 = cols as i32 - 1;
    
    while (i as usize) < rows && j >= 0
        invariant
            0 <= i <= rows as i32,
            -1 <= j < cols as i32,
            (forall|k: int, l: int| 0 <= k < i as int && 0 <= l < cols as int ==> 0 <= k < a.len() as int && 0 <= l < a[0].len() as int && a[k][l] != key),
            (forall|k: int, l: int| (j as int) < l && l < cols as int && 0 <= k < rows as int ==> 0 <= k < a.len() as int && 0 <= l < a[0].len() as int && a[k][l] != key)
        decreases (rows as i32 - i) + j + 1
    {
        let b = check_bounds(i, j, rows, cols);
        let current = a[i as usize][j as usize];
        if current == key {
            return (i, j);
        } else if current < key {
            i += 1;
        } else {
            j -= 1;
        }
    }
    
    (-1, -1)
}
// </vc-code>

}
fn main() {}