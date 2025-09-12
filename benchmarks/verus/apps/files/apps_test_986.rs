// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, k: int, requests: Seq<int>) -> bool {
    n >= 1 && k >= 1 && requests.len() == n &&
    forall|i: int| 0 <= i < requests.len() ==> 1 <= requests[i] <= n
}

spec fn valid_solution(n: int, k: int, requests: Seq<int>, cost: int) -> bool {
    valid_input(n, k, requests) && cost >= 0 && cost <= n
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int, requests: Seq<int>) -> (cost: int)
    requires valid_input(n, k, requests)
    ensures valid_solution(n, k, requests, cost)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}