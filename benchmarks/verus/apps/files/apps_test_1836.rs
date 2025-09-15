// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, edges: Seq<(int, int)>) -> bool {
    n >= 2 &&
    forall|i: int| 0 <= i < edges.len() ==> 1 <= edges[i].0 <= n && 1 <= edges[i].1 <= n && edges[i].0 != edges[i].1
}

spec fn valid_output(result: int, n: int, edges: Seq<(int, int)>) -> bool {
    result >= 0 && result <= 2 * edges.len() * (edges.len() + 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, edges: Seq<(int, int)>) -> (result: int)
    requires valid_input(n, edges)
    ensures valid_output(result, n, edges)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}