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
/* helper modified by LLM (iteration 5): trivial index bounds lemma to assist reasoning about int indices */
proof fn index_bounds_i(i: int, len: int)
    requires
        0 <= i,
        i < len,
    ensures
        0 <= i,
        i < len,
{
    proof {
        assert(0 <= i);
        assert(i < len);
    }
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
    /* code modified by LLM (iteration 5): use int indices for loops and proper invariants */
    let mut r: int = 0;
    while r < a.len()
        invariant
            0 <= r,
            r <= a.len(),
            (forall|ri: int, cj: int| 0 <= ri < r && 0 <= cj < a[ri].len() ==> #[trigger] a[ri][cj] != key),
        decreases a.len() - r
    {
        let mut c: int = 0;
        while c < a[r].len()
            invariant
                0 <= c,
                c <= a[r].len(),
                (forall|cj: int| 0 <= cj < c ==> #[trigger] a[r][cj] != key),
            decreases a[r].len() - c
        {
            let v: i32 = a[r][c];
            if v == key {
                return (r as i32, c as i32);
            }
            c = c + 1;
        }
        r = r + 1;
    }

    (-1i32, -1i32)
}
// </vc-code>

}
fn main() {}