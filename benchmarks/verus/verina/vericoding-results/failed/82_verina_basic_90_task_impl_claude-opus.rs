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
    /* code modified by LLM (iteration 5): fixed cast issues and invariant initialization */
    let rows = a.len();
    let cols = a[0].len();
    
    if cols == 0 {
        return (-1, -1);
    }
    
    let mut i: usize = 0;
    let mut j: i32 = #[verifier::truncate] (cols - 1) as i32;
    
    // Initial assertions to establish invariants
    assert(0 <= i <= rows);
    assert(0 <= j < cols);
    assert(forall|r: int, c: int| 0 <= r < i && 0 <= c < cols ==> #[trigger] a[r][c] != key) by {
        // Vacuously true since i == 0
    }
    assert(forall|r: int, c: int| 0 <= r < rows && (j as int) < c < cols ==> #[trigger] a[r][c] != key) by {
        // Vacuously true since j == cols - 1
    }
    
    while i < rows && j >= 0
        invariant
            0 <= i <= rows,
            -1 <= j < cols,
            forall|r: int, c: int| 0 <= r < i && 0 <= c < cols ==> #[trigger] a[r][c] != key,
            forall|r: int, c: int| 0 <= r < rows && (j as int) < c < cols ==> #[trigger] a[r][c] != key,
            slope_search_precond(a, key),
        decreases (rows - i) + (j + 1) as usize,
    {
        assert(0 <= i < a.len());
        assert(0 <= j < a[i].len());
        let current = a[i][j as usize];
        
        if current == key {
            assert(i >= 0 && i < a.len() && j >= 0 && j < a[0].len());
            assert(a[i as int][j as int] == key);
            return (i as i32, j);
        } else if current > key {
            j = j - 1;
        } else {
            i = i + 1;
        }
    }
    
    assert(i >= rows || j < 0);
    assert(forall|r: int, c: int| 0 <= r < rows && 0 <= c < cols ==> #[trigger] a[r][c] != key);
    return (-1, -1);
}
// </vc-code>

}
fn main() {}