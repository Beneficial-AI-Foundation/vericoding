// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, queries: Seq<(int, int)>) -> bool {
    n > 0 && 
    forall|i: int| 0 <= i < queries.len() ==> #[trigger] queries[i].0 >= 1 && #[trigger] queries[i].0 <= n && #[trigger] queries[i].1 >= 1 && #[trigger] queries[i].1 <= n
}

spec fn chessboard_value(n: int, x: int, y: int) -> int {
    if (x + y) % 2 == 0 {
        1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2
    } else {
        (n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2
    }
}

spec fn valid_result(n: int, queries: Seq<(int, int)>, results: Seq<int>) -> bool {
    valid_input(n, queries) ==> (
        results.len() == queries.len() &&
        forall|i: int| 0 <= i < queries.len() ==> {
            let x = #[trigger] queries[i].0 - 1;
            let y = #[trigger] queries[i].1 - 1;
            0 <= x < n && 0 <= y < n &&
            #[trigger] results[i] == chessboard_value(n, x, y)
        }
    )
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, queries: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(n as int, queries@.map(|i: int, q: (i8, i8)| (q.0 as int, q.1 as int)))
    ensures valid_result(n as int, queries@.map(|i: int, q: (i8, i8)| (q.0 as int, q.1 as int)), results@.map(|i: int, r: i8| r as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}