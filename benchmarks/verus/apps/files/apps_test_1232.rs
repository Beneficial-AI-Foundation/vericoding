// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n_a: int, n_b: int, k: int, m: int, a: Seq<int>, b: Seq<int>) -> bool {
    n_a >= 1 && n_b >= 1 &&
    k >= 1 && k <= n_a &&
    m >= 1 && m <= n_b &&
    a.len() == n_a &&
    b.len() == n_b
}

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> #[trigger] s.index(i) <= #[trigger] s.index(j)
}

spec fn valid_selection(a: Seq<int>, b: Seq<int>, k: int, m: int) -> bool
    recommends k >= 1 && k <= a.len() && m >= 1 && m <= b.len()
{
    a[k - 1] < b[b.len() - m]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n_a: i8, n_b: i8, k: i8, m: i8, a: Vec<i8>, b: Vec<i8>) -> (result: &'static str)
    requires 
        valid_input(n_a as int, n_b as int, k as int, m as int, a@.map(|i, x: i8| x as int), b@.map(|i, x: i8| x as int)),
        is_sorted(a@.map(|i, x: i8| x as int)),
        is_sorted(b@.map(|i, x: i8| x as int))
    ensures 
        result == "YES" || result == "NO",
        result == "YES" <==> valid_selection(a@.map(|i, x: i8| x as int), b@.map(|i, x: i8| x as int), k as int, m as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}