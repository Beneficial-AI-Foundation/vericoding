// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_starting_point(gas: &Vec<i32>, cost: &Vec<i32>, start: int) -> bool 
{
    0 <= start < gas.len() && 
    forall|i: int| 0 <= i < gas.len() ==> {
        #[trigger] calculate_acc(gas, cost, start, i + 1) >= 0
    }
}

spec fn calculate_acc(gas: &Vec<i32>, cost: &Vec<i32>, start: int, steps: int) -> int
    decreases steps
{
    if steps <= 0 {
        0
    } else {
        let prev_acc = calculate_acc(gas, cost, start, steps - 1);
        let jdx = ((start + (steps - 1)) % (gas.len() as int)) as nat % (gas.len() as nat);
        prev_acc + gas[jdx as int] - cost[jdx as int]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax errors and improved proof structure */
proof fn calculate_acc_nonnegative(gas: &Vec<i32>, cost: &Vec<i32>, start: int, steps: int) -> (acc: int)
    decreases steps
    requires
        0 <= start < gas.len(),
        0 <= steps <= gas.len(),
        forall|i: int| 0 <= i < gas.len() ==> #[trigger] calculate_acc(gas, cost, start, i + 1) >= 0
    ensures
        acc >= 0,
        acc == calculate_acc(gas, cost, start, steps)
{
    if steps == 0 {
        0
    } else {
        let prev = calculate_acc_nonnegative(gas, cost, start, steps - 1);
        let jdx = ((start + (steps - 1)) % (gas.len() as int)) as nat % (gas.len() as nat);
        let current = gas[jdx as int] - cost[jdx as int];
        prev + current
    }
}

proof fn valid_starting_point_implies_completes(gas: &Vec<i32>, cost: &Vec<i32>, start: int)
    requires
        gas.len() == cost.len(),
        gas.len() > 0,
        0 <= start < gas.len(),
        valid_starting_point(gas, cost, start)
    ensures
        calculate_acc(gas, cost, start, gas.len() as int) >= 0
{
    calculate_acc_nonnegative(gas, cost, start, gas.len() as int);
}
// </vc-helpers>

// <vc-spec>
fn can_complete_circuit(gas: &Vec<i32>, cost: &Vec<i32>) -> (result: i32)
    requires 
        gas.len() == cost.len(),
        gas.len() > 0,
    ensures
        (result == -1) ==> (forall|start: int| 0 <= start < gas.len() ==> !valid_starting_point(gas, cost, start)),
        (result >= 0) ==> (
            0 <= result < gas.len() &&
            valid_starting_point(gas, cost, result as int) &&
            (forall|start: int| 0 <= start < result ==> !valid_starting_point(gas, cost, start))
        ),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed incorrect requires clause and added proper implementation */
{
    let n = gas.len() as i32;
    let mut total_gas = 0;
    let mut total_cost = 0;
    let mut current_gas = 0;
    let mut start_index = 0;
    
    for i in 0..gas.len() {
        total_gas += gas[i];
        total_cost += cost[i];
    }
    
    if total_gas < total_cost {
        return -1;
    }
    
    for i in 0..gas.len() {
        current_gas += gas[i] - cost[i];
        if current_gas < 0 {
            start_index = (i + 1) as i32;
            current_gas = 0;
        }
    }
    
    start_index
}
// </vc-code>

}
fn main() {}