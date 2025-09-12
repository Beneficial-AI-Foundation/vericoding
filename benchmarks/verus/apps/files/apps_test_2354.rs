// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, queries: Seq<(int, int)>) -> bool {
    n > 0 && 
    forall|i: int| 0 <= i < queries.len() ==> 1 <= queries[i].0 <= n && 1 <= queries[i].1 <= n
}

spec fn chessboard_value(n: int, x: int, y: int) -> int
    recommends n > 0, 0 <= x < n && 0 <= y < n
{
    if (x + y) % 2 == 0 {
        1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2
    } else {
        (n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2
    }
}

spec fn valid_result(n: int, queries: Seq<(int, int)>, results: Seq<int>) -> bool
    recommends valid_input(n, queries)
{
    results.len() == queries.len() &&
    forall|i: int| 0 <= i < queries.len() ==> {
        let x = queries[i].0 - 1;
        let y = queries[i].1 - 1;
        0 <= x < n && 0 <= y < n &&
        results[i] == chessboard_value(n, x, y)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, queries: Seq<(int, int)>) -> (results: Seq<int>)
    requires valid_input(n, queries)
    ensures valid_result(n, queries, results)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}