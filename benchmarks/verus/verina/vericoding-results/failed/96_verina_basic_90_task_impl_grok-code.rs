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
    /* code modified by LLM (iteration 5): fixed compilation errors by correcting Tracked type capitalization and proper Tracked construction */
    let mut i: i32 = (a.len() - 1) as i32;
    let mut j: i32 = 0;
    let mut g_i: Tracked<int> = Tracked(i as int);
    let mut g_j: Tracked<int> = Tracked(j as int);
    let width: i32 = a[0].len() as i32;
    while i >= 0 && j < width
        invariant(i as int == g_i@);
        invariant(j as int == g_j@);
        decreases(g_i@, -(g_j@));
    {
        let val = a[i as usize][j as usize];
        if val == key {
            return (i, j);
        } else if val < key {
            j += 1;
            proof {
                g_j = Tracked(g_j@ + 1);
            }
        } else {
            i -= 1;
            proof {
                g_i = Tracked(g_i@ - 1);
            }
        }
    }
    (-1, -1)
}
// </vc-code>

}
fn main() {}