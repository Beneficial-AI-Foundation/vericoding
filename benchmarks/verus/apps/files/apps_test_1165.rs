// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, m: int, a: Seq<int>, queries: Seq<(int, int, int)>) -> bool {
    n > 0 && m >= 0 && a.len() == n && queries.len() == m &&
    forall|q: (int, int, int)| queries.contains(q) ==> 1 <= q.0 <= q.1 <= n
}

spec fn valid_result(a: Seq<int>, queries: Seq<(int, int, int)>, result: Seq<int>) -> bool {
    result.len() == queries.len() &&
    forall|i: int| 0 <= i < queries.len() ==> {
        let (l, r, x) = queries[i];
        (result[i] == -1 ==> (forall|j: int| l <= j <= r ==> 0 <= j-1 < a.len() && a[j-1] == x)) &&
        (result[i] != -1 ==> l <= result[i] <= r && 0 <= result[i]-1 < a.len() && a[result[i]-1] != x)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int, a: Seq<int>, queries: Seq<(int, int, int)>) -> (result: Seq<int>)
    requires valid_input(n, m, a, queries)
    ensures valid_result(a, queries, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}