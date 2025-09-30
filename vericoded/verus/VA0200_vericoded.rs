// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, requests: Seq<int>) -> bool {
    n >= 1 && k >= 1 && requests.len() == n &&
    forall|i: int| 0 <= i < requests.len() ==> #[trigger] requests[i] >= 1 && #[trigger] requests[i] <= n
}

spec fn valid_solution(n: int, k: int, requests: Seq<int>, cost: int) -> bool {
    valid_input(n, k, requests) && cost >= 0 && cost <= n
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, requests: Vec<i8>) -> (cost: i8)
    requires valid_input(n as int, k as int, requests@.map(|i: int, x: i8| x as int))
    ensures valid_solution(n as int, k as int, requests@.map(|i: int, x: i8| x as int), cost as int)
// </vc-spec>
// <vc-code>
{
    0i8
}
// </vc-code>


}

fn main() {}