// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_cost_tickets(days: Vec<nat>, costs: Vec<nat>) -> (result: nat)
    requires 
        days.len() > 0,
        costs.len() == 3,
        forall|i: int| 0 <= i < days.len() ==> #[trigger] days[i] >= 1 && #[trigger] days[i] <= 365,
        forall|i: int| 0 <= i < costs.len() ==> #[trigger] costs[i] >= 1 && #[trigger] costs[i] <= 1000,
        forall|i: int, j: int| 0 <= i < j < days.len() ==> #[trigger] days[i] < #[trigger] days[j],
    ensures
        result >= if costs[0] <= costs[1]/7 && costs[0] <= costs[2]/30 { costs[0] * days.len() } 
                  else if costs[1]/7 <= costs[2]/30 { (costs[1]/7) * days.len() }
                  else { (costs[2]/30) * days.len() },
        result <= costs[0] * days.len()
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
    // println!("{}", min_cost_tickets(vec![1, 4, 6, 7, 8, 20], vec![2, 7, 15]));
    // println!("{}", min_cost_tickets(vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 30, 31], vec![2, 7, 15]));
}