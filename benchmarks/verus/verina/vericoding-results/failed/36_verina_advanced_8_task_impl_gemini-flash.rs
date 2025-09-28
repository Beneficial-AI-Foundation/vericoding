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
/* helper modified by LLM (iteration 5): Corrected type annotations and ensured `Vec` indexing is done with `usize`. */
spec fn calculate_total_circuit_sum(gas: &Vec<i32>, cost: &Vec<i32>) -> int
    requires
        gas.len() == cost.len(),
        gas.len() > 0,
{
    let n = gas.len();
    let mut total_sum: int = 0;
    for i in 0..n {
        total_sum = total_sum + (gas[i] as int) - (cost[i] as int);
    }
    total_sum
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
/* code modified by LLM (iteration 5): Corrected type annotations for `total_sum` and array indexing as well as the calculation in the `if` condition using the helper function. */
{
    let n = gas.len();

    if calculate_total_circuit_sum(gas, cost) < 0 {
        return -1;
    }

    let mut start_index: usize = 0;
    let mut current_gas: int = 0;

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            i <= n,
            0 <= start_index as int,
            start_index < n,
            current_gas == calculate_acc(gas, cost, start_index as int, (i - start_index) as int),
    {
        current_gas = current_gas + (gas[i] as int) - (cost[i] as int);

        if current_gas < 0 {
            start_index = i + 1;
            current_gas = 0;
        }
        i = i + 1;
    }

    start_index as i32
}
// </vc-code>

}
fn main() {}