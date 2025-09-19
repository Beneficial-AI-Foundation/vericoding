// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn max_profit_in_list(profit: Seq<i32>) -> i32
    decreases profit.len()
{
    if profit.len() == 0 {
        0
    } else {
        if profit[0] > max_profit_in_list(profit.skip(1)) {
            profit[0]
        } else {
            max_profit_in_list(profit.skip(1))
        }
    }
}

fn max_profit_assignment(difficulty: Vec<i32>, profit: Vec<i32>, worker: Vec<i32>) -> (result: i32)
    requires 
        difficulty.len() == profit.len(),
        forall|i: int| 0 <= i < difficulty.len() ==> 1 <= difficulty[i] && difficulty[i] <= 100000,
        forall|i: int| 0 <= i < profit.len() ==> 1 <= profit[i] && profit[i] <= 100000,
        forall|i: int| 0 <= i < worker.len() ==> 1 <= worker[i] && worker[i] <= 100000,
    ensures 
        result >= 0,
        result <= max_profit_in_list(profit@) * (worker.len() as i32),
        (forall|i: int| 0 <= i < worker.len() ==> worker[i] == 0) ==> result == 0,
        (forall|i: int| 0 <= i < worker.len() ==> worker[i] >= 100) ==> 
            result == (worker.len() as i32) * max_profit_in_list(profit@)
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
    // let result1 = max_profit_assignment(vec![2, 4, 6, 8, 10], vec![10, 20, 30, 40, 50], vec![4, 5, 6, 7]);
    // println!("{}", result1); // Expected: 100

    // let result2 = max_profit_assignment(vec![1, 2, 3], vec![10, 20, 30], vec![1, 2]);  
    // println!("{}", result2); // Expected: 30

    // let result3 = max_profit_assignment(vec![5], vec![100], vec![1, 2, 3]);
    // println!("{}", result3); // Expected: 0
}