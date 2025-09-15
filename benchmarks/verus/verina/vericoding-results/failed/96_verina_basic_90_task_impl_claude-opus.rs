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
    /* code modified by LLM (iteration 5): fixed type mismatch in assert */
    let rows = a.len();
    let cols = a[0].len();
    
    let mut i: usize = 0;
    let mut j: i32 = if cols > 0 { (cols - 1) as i32 } else { -1 };
    
    while i < rows && j >= 0
        invariant
            0 <= i <= rows,
            -1 <= j,
            j < cols as i32,
            cols > 0,
            forall|r: int| 0 <= r < a.len() ==> #[trigger] a[r].len() == cols,
            forall|r: int, c: int| 0 <= r < i as int && 0 <= c < cols as int ==> #[trigger] a[r][c] != key,
            forall|r: int, c: int| 0 <= r < rows as int && (j + 1) <= c && c < cols as int ==> #[trigger] a[r][c] != key,
        decreases (rows - i) as int + j + 1
    {
        assert(0 <= i < a.len());
        assert(0 <= j < a[i].len() as i32);
        
        if a[i][j as usize] == key {
            return (i as i32, j);
        } else if a[i][j as usize] < key {
            i = i + 1;
        } else {
            j = j - 1;
        }
    }
    
    assert(i == rows || j == -1);
    assert(forall|r: int, c: int| 0 <= r < rows as int && 0 <= c < cols as int ==> #[trigger] a[r][c] != key);
    return (-1, -1);
}
// </vc-code>

}
fn main() {}