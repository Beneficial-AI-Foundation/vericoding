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
/* helper modified by LLM (iteration 5): Removed unnecessary helper, as the logic is within the main function. */
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
/* code modified by LLM (iteration 5): Corrected loop invariant by adding one for elements already checked, fixed postcondition to handle out-of-bounds access. */
{
    if a.len() == 0 || a[0].len() == 0 {
        return (-1, -1);
    }

    let mut r: usize = 0;
    let mut c: usize = a[0].len() - 1;

    while r < a.len() && c < a[0].len()
        invariant
            0 <= r as int,
            r <= a.len(),
            0 <= c as int,
            c < a[0].len(),
            slope_search_precond(a, key),
            // All elements (i,j) such that i < r and j is anything, or i is r and j > c, are not the key.
            forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[0].len() && 
                ((i < r as int) || (i == r as int && j > c as int)) 
                ==> #[trigger] a[i][j] != key,
        decreases (a.len() - r as int) + (c as int + 1)
    {
        let current_val = a[r][c];
        if current_val == key {
            return (r as i32, c as i32);
        } else if current_val < key {
            r = r + 1;
        } else { // current_val > key
            c = c - 1;
        }
    }

    (-1, -1)
}
// </vc-code>

}
fn main() {}