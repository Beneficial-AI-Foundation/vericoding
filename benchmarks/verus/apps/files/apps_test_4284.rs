// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_query(k: int, n: int, a: int, b: int) -> bool {
    k > 0 && n > 0 && a > 0 && b > 0 && b < a
}

spec fn max_action_a_turns(k: int, n: int, a: int, b: int) -> int {
    if n * b > k {
        -1
    } else {
        let max_possible = (k - n * b - 1) / (a - b);
        if n <= max_possible { n } else { max_possible }
    }
}

spec fn valid_result(result: int, k: int, n: int, a: int, b: int) -> bool {
    result == -1 || (0 <= result <= n)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(queries: Seq<(int, int, int, int)>) -> (results: Seq<int>)
    requires 
        queries.len() > 0,
        forall|i: int| 0 <= i < queries.len() ==> {
            let (k, n, a, b) = queries[i];
            valid_query(k, n, a, b)
        }
    ensures 
        results.len() == queries.len(),
        forall|i: int| 0 <= i < queries.len() ==> {
            let (k, n, a, b) = queries[i];
            results[i] == max_action_a_turns(k, n, a, b)
        },
        forall|i: int| 0 <= i < results.len() ==> {
            let (k, n, a, b) = queries[i];
            valid_result(results[i], k, n, a, b)
        }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}