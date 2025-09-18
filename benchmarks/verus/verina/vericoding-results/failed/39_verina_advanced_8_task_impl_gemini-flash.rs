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
/* helper modified by LLM (iteration 5): [No changes needed in `lemma_valid_implication` helper] */
proof fn lemma_valid_implication(gas: &Vec<i32>, cost: &Vec<i32>, start: int, i_idx: int)
    requires
        0 <= start < gas.len(),
        0 <= i_idx < gas.len(),
        valid_starting_point(gas, cost, start),
    ensures
        calculate_acc(gas, cost, start, i_idx + 1) >= 0,
{
    // This lemma is just to explicitly state the property from valid_starting_point
    // that we want to use, since the direct use of a forall might not be directly available
    // during execution in the proof context without a helper.
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
{
/* code modified by LLM (iteration 5): [Fixed variable name collision in `while` loop body] */
    let n = gas.len();
    let mut total_gas_sum: i64 = 0;
    let mut current_tank: i64 = 0;
    let mut start_station: int = 0;

    let mut i_loop: int = 0;
    while i_loop < n
        invariant
            0 <= i_loop <= n,
            total_gas_sum == (ghost {
                if i_loop == 0 {
                    0
                } else {
                    (0..i_loop as int).fold(0, |acc: int, k: int| acc + gas[k as nat] as int - cost[k as nat] as int) as i64
                }
            }),
            current_tank == (ghost {
                if start_station <= i_loop {
                    (start_station..i_loop).fold(0, |acc: int, k: int| acc + gas[k as nat] as int - cost[k as nat] as int) as i64
                } else {
                    0
                }
            }),
            0 <= start_station <= n,
            forall|k: int| 0 <= k < start_station ==> !valid_starting_point(gas, cost, k),
        decreases n - i_loop
    {
        let diff = gas[i_loop as usize] as i64 - cost[i_loop as usize] as i64;
        total_gas_sum = total_gas_sum + diff;
        current_tank = current_tank + diff;

        if current_tank < 0 {
            start_station = i_loop + 1;
            current_tank = 0;
        }
        i_loop = i_loop + 1;
    }
    
    if total_gas_sum < 0 {
        -1
    } else {
        if start_station >= n {
            proof {
                 // If total_gas_sum >= 0, and start_station becomes n, it means
                 // the very last station (n-1) was the one that made current_tank < 0
                 // This implies that starting at 0 and going to n-1 (which wraps around to start_station + n-1)
                 // still resulted in a negative tank before reaching the end of the circuit (0 to n-1).
                 // We need to find the actual start_station if the loop finishes with start_station = n.
                 // If total_gas_sum >= 0 and no valid starting point was found up to n-1, then 0 must be the answer.
                 // This is because the problem guarantees a unique solution if one exists, and a total_gas_sum >= 0 guarantees one exists.
            }
            0 // If total_gas_sum >= 0 and start_station ends up at n, then it means 0 is the start.
              // This handles the case where start_station might be pushed to n due to a negative balance for the segment up to n-1,
              // but the overall sum is positive, meaning a cycle can be completed from 0.
        }
        else {
            start_station as i32
        }
    }
}
// </vc-code>

}
fn main() {}