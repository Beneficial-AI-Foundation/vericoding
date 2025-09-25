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
fn solve(n: i8, edges: Vec<(i8, i8)>) -> (result: i8)
    requires 
        valid_input(n as int, edges@.map(|e: (i8, i8)| -> (int, int) { (e.0 as int, e.1 as int) }))
    ensures 
        valid_output(result as int, n as int, edges@.map(|e: (i8, i8)| -> (int, int) { (e.0 as int, e.1 as int) }))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}