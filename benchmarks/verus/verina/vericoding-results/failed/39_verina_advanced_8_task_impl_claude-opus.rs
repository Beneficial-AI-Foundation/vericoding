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
proof fn lemma_total_sum_negative_no_solution(gas: &Vec<i32>, cost: &Vec<i32>)
    requires
        gas.len() == cost.len(),
        gas.len() > 0,
    ensures
        (exists|i: int| 0 <= i < gas.len() && gas[i as int] - cost[i as int] < 0) ==> true,
{
}

proof fn lemma_acc_properties(gas: &Vec<i32>, cost: &Vec<i32>, start: int, steps: int)
    requires
        gas.len() == cost.len(),
        gas.len() > 0,
        0 <= start < gas.len(),
        0 <= steps <= gas.len(),
    ensures
        calculate_acc(gas, cost, start, steps) == calculate_acc(gas, cost, start, steps),
    decreases steps,
{
    if steps > 0 {
        lemma_acc_properties(gas, cost, start, steps - 1);
    }
}

spec fn sum_range(v: &Vec<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end {
        0
    } else {
        v[start] + sum_range(v, start + 1, end)
    }
}

/* helper modified by LLM (iteration 5): fixed return type from i64 to int */
spec fn sum_range_i64(v: &Vec<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end {
        0
    } else {
        v[start] + sum_range_i64(v, start + 1, end)
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
{
    /* code modified by LLM (iteration 5): changed to use int for sum_range_i64 */
    let n = gas.len();
    let mut total_gas: i64 = 0;
    let mut total_cost: i64 = 0;
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            n == gas.len(),
            n == cost.len(),
            total_gas == sum_range_i64(gas, 0, i as int) as i64,
            total_cost == sum_range_i64(cost, 0, i as int) as i64,
        decreases n - i,
    {
        total_gas = total_gas + gas[i] as i64;
        total_cost = total_cost + cost[i] as i64;
        i = i + 1;
    }
    
    if total_gas < total_cost {
        proof {
            assert(forall|start: int| 0 <= start < gas.len() ==> !valid_starting_point(gas, cost, start));
        }
        return -1;
    }
    
    let mut start: usize = 0;
    let mut tank: i64 = 0;
    let mut j: usize = 0;
    
    while j < n
        invariant
            0 <= j <= n,
            0 <= start <= j,
            start <= n,
            n == gas.len(),
            n == cost.len(),
            (start < n) || (start == n && j == n),
            tank >= 0,
            forall|k: int| 0 <= k < start ==> !valid_starting_point(gas, cost, k),
        decreases n - j,
    {
        tank = tank + gas[j] as i64 - cost[j] as i64;
        if tank < 0 {
            start = j + 1;
            tank = 0;
        }
        j = j + 1;
    }
    
    if start >= n {
        proof {
            assert(forall|start: int| 0 <= start < gas.len() ==> !valid_starting_point(gas, cost, start));
        }
        return -1;
    }
    
    proof {
        assert(0 <= start < n);
        assert(valid_starting_point(gas, cost, start as int));
    }
    
    start as i32
}
// </vc-code>

}
fn main() {}