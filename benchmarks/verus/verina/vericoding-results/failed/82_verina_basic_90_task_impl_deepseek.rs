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
/* helper modified by LLM (iteration 5): Fixed compilation errors and improved specifications */
proof fn lemma_sorted_array_not_contains(a: Seq<Seq<i32>>, key: i32, i: int, j: int)
    requires
        a.len() > 0,
        forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k].len() == a[0].len(),
        forall|k: int, l: int| 0 <= k < a.len() && 0 <= l < a[k].len() - 1 ==> #[trigger] a[k][l] <= a[k][l + 1],
        forall|l: int, k: int| 0 <= l < a[0].len() && 0 <= k < a.len() - 1 ==> #[trigger] a[k][l] <= a[k + 1][l],
        0 <= i < a.len(),
        0 <= j < a[0].len(),
        a[i][j] > key,
    ensures forall|k: int, l: int| 0 <= k <= i && 0 <= l <= j ==> #[trigger] a[k][l] > key
{
}

proof fn lemma_sorted_array_not_contains_rev(a: Seq<Seq<i32>>, key: i32, i: int, j: int)
    requires
        a.len() > 0,
        forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k].len() == a[0].len(),
        forall|k: int, l: int| 0 <= k < a.len() && 0 <= l < a[k].len() - 1 ==> #[trigger] a[k][l] <= a[k][l + 1],
        forall|l: int, k: int| 0 <= l < a[0].len() && 0 <= k < a.len() - 1 ==> #[trigger] a[k][l] <= a[k + 1][l],
        0 <= i < a.len(),
        0 <= j < a[0].len(),
        a[i][j] < key,
    ensures forall|k: int, l: int| i <= k < a.len() && j <= l < a[0].len() ==> #[trigger] a[k][l] < key
{
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
/* code modified by LLM (iteration 5): Fixed compilation errors with array indexing */
{
    let m: usize = a.len();
    let n: usize = a[0].len();
    let mut i: i32 = 0;
    let mut j: i32 = n as i32 - 1;
    
    while i < m as i32 && j >= 0
        invariant
            0 <= i <= m as i32,
            -1 <= j < n as i32,
            forall|k: int, l: int| 0 <= k < i as int && 0 <= l < n as int ==> #[trigger] a[k][l] < key,
            forall|k: int, l: int| i as int <= k < m as int && j as int + 1 <= l < n as int ==> #[trigger] a[k][l] > key
        decreases (m as int - i as int) + (j as int + 1)
    {
        assert(0 <= i < m as i32);
        assert(0 <= j < n as i32);
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