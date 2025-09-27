// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_coal_containers(n: usize, k: usize, costs: Vec<usize>) -> (result: usize)
    requires 
        n > 0,
        k > 0,
        costs.len() == n,
        forall|i: int| 0 <= i < costs.len() ==> costs[i] >= 1 && costs[i] <= 1000,
    ensures 
        result >= 1,
        result <= n,
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

fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible

    // #eval solve_coal_containers(3, 2, vec![5, 4, 7]) should return 2
    // #eval solve_coal_containers(5, 1, vec![5, 3, 4, 5, 6]) should return 1
}