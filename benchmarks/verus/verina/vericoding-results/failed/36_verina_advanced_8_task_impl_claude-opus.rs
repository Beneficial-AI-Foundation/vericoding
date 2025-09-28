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
/* helper modified by LLM (iteration 5): Fixed trigger issue in lemma_invalid_start_implies_invalid_later */
proof fn lemma_invalid_start_implies_invalid_later(gas: &Vec<i32>, cost: &Vec<i32>, start: int, k: int)
    requires
        gas.len() == cost.len(),
        gas.len() > 0,
        0 <= start < gas.len(),
        0 <= k < gas.len(),
        calculate_acc(gas, cost, start, k + 1) < 0,
    ensures
        forall|j: int| k < j < gas.len() ==> #[trigger] calculate_acc(gas, cost, start, j + 1) < calculate_acc(gas, cost, start, k + 1),
    decreases gas.len() - k - 1,
{
    if k + 1 < gas.len() {
        let next_idx = ((start + k + 1) % (gas.len() as int)) as nat % (gas.len() as nat);
        assert(calculate_acc(gas, cost, start, k + 2) == calculate_acc(gas, cost, start, k + 1) + gas[next_idx as int] - cost[next_idx as int]);
        if calculate_acc(gas, cost, start, k + 2) >= calculate_acc(gas, cost, start, k + 1) {
            lemma_invalid_start_implies_invalid_later(gas, cost, start, k + 1);
        }
    }
}

proof fn lemma_total_sum_property(gas: &Vec<i32>, cost: &Vec<i32>)
    requires
        gas.len() == cost.len(),
        gas.len() > 0,
    ensures
        forall|start: int| 0 <= start < gas.len() ==> calculate_acc(gas, cost, start, gas.len() as int) == calculate_acc(gas, cost, 0, gas.len() as int),
{
    assert forall|start: int| 0 <= start < gas.len() implies calculate_acc(gas, cost, start, gas.len() as int) == calculate_acc(gas, cost, 0, gas.len() as int) by {
        lemma_sum_rotation(gas, cost, start, gas.len() as int);
    }
}

proof fn lemma_sum_rotation(gas: &Vec<i32>, cost: &Vec<i32>, start: int, n: int)
    requires
        gas.len() == cost.len(),
        gas.len() > 0,
        0 <= start < gas.len(),
        n == gas.len(),
    ensures
        calculate_acc(gas, cost, start, n) == calculate_acc(gas, cost, 0, n),
    decreases n,
{
    if n == 0 {
        assert(calculate_acc(gas, cost, start, 0) == 0);
        assert(calculate_acc(gas, cost, 0, 0) == 0);
    } else {
        lemma_sum_rotation(gas, cost, start, n - 1);
        let idx_start = ((start + (n - 1)) % (gas.len() as int)) as nat % (gas.len() as nat);
        let idx_zero = ((n - 1) % (gas.len() as int)) as nat % (gas.len() as nat);
        assert(idx_start == idx_zero);
        assert(calculate_acc(gas, cost, start, n) == calculate_acc(gas, cost, start, n - 1) + gas[idx_start as int] - cost[idx_start as int]);
        assert(calculate_acc(gas, cost, 0, n) == calculate_acc(gas, cost, 0, n - 1) + gas[idx_zero as int] - cost[idx_zero as int]);
    }
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
/* code modified by LLM (iteration 5): No change needed in main code */
{
    let n = gas.len();
    let mut total_tank = 0i32;
    let mut curr_tank = 0i32;
    let mut starting_station = 0i32;
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            0 <= starting_station < n,
            total_tank == calculate_acc(gas, cost, 0, i as int),
            curr_tank == calculate_acc(gas, cost, starting_station as int, (i - starting_station) as int),
            curr_tank >= 0,
            forall|k: int| 0 <= k < starting_station ==> exists|j: int| 0 <= j < n && calculate_acc(gas, cost, k, j + 1) < 0,
        decreases n - i
    {
        total_tank = total_tank + gas[i] - cost[i];
        curr_tank = curr_tank + gas[i] - cost[i];
        
        if curr_tank < 0 {
            proof {
                lemma_invalid_start_implies_invalid_later(gas, cost, starting_station as int, (i - starting_station) as int);
            }
            starting_station = (i + 1) as i32;
            curr_tank = 0;
        }
        i = i + 1;
    }
    
    proof {
        lemma_total_sum_property(gas, cost);
    }
    
    if total_tank >= 0 {
        assert(calculate_acc(gas, cost, 0, n as int) >= 0);
        assert(calculate_acc(gas, cost, starting_station as int, n as int) >= 0);
        assert(valid_starting_point(gas, cost, starting_station as int));
        starting_station
    } else {
        assert(calculate_acc(gas, cost, 0, n as int) < 0);
        assert(forall|start: int| 0 <= start < n ==> calculate_acc(gas, cost, start, n as int) < 0);
        assert(forall|start: int| 0 <= start < n ==> !valid_starting_point(gas, cost, start));
        -1
    }
}
// </vc-code>

}
fn main() {}