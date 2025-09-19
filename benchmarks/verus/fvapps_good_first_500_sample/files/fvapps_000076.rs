// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn list_sum(costs: Seq<nat>) -> nat
    decreases costs.len()
{
    if costs.len() == 0 {
        0
    } else {
        costs[0] + list_sum(costs.drop_first())
    }
}
// </vc-helpers>

// <vc-spec>
fn solve_fence(heights: Vec<nat>, costs: Vec<nat>) -> (result: nat)
    requires heights.len() == costs.len(),
    ensures 
        result >= 0,
        heights.len() <= 1 ==> result == 0,
        result <= list_sum(costs@.map_values(|c: nat| c * 2))
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
    // let result1 = solve_fence(vec![2, 2, 3], vec![4, 1, 5]);
    // println!("Result 1: {}", result1); // Expected: 2
    
    // let result2 = solve_fence(vec![2, 2, 2], vec![3, 10, 6]);
    // println!("Result 2: {}", result2); // Expected: 9
    
    // let result3 = solve_fence(vec![1, 3, 2, 1000000000], vec![7, 3, 6, 2]);
    // println!("Result 3: {}", result3); // Expected: 0
}