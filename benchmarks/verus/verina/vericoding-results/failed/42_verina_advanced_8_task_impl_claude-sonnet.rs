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
proof fn acc_calculation_bound(gas: &Vec<i32>, cost: &Vec<i32>, start: int, steps: int)
    requires 0 <= start < gas.len(), 0 <= steps <= gas.len()
    ensures calculate_acc(gas, cost, start, steps) == calculate_acc(gas, cost, start, steps)
{
}

proof fn valid_starting_point_complete_circuit(gas: &Vec<i32>, cost: &Vec<i32>, start: int)
    requires 0 <= start < gas.len(), valid_starting_point(gas, cost, start)
    ensures forall|i: int| 0 <= i < gas.len() ==> #[trigger] calculate_acc(gas, cost, start, i + 1) >= 0
{
    proof {
        assert(forall|i: int| 0 <= i < gas.len() ==> #[trigger] calculate_acc(gas, cost, start, i + 1) >= 0) by {
            valid_starting_point(gas, cost, start);
        }
    }
}

/* helper modified by LLM (iteration 5): fixed indexing with proper bracket syntax */
fn check_valid_starting_point(gas: &Vec<i32>, cost: &Vec<i32>, start: usize) -> (result: bool)
    requires 
        gas.len() == cost.len(),
        gas.len() > 0,
        start < gas.len()
    ensures
        result == valid_starting_point(gas, cost, start as int)
{
    let mut acc: i64 = 0;
    let mut i = 0;
    while i < gas.len()
        invariant
            0 <= i <= gas.len(),
            acc == calculate_acc(gas, cost, start as int, i as int),
            forall|j: int| 0 <= j < i ==> #[trigger] calculate_acc(gas, cost, start as int, j + 1) >= 0
        decreases gas.len() - i
    {
        let jdx = (start + i) % gas.len();
        acc = acc + gas[jdx] as i64 - cost[jdx] as i64;
        if acc < 0 {
            return false;
        }
        i = i + 1;
    }
    true
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
    /* code modified by LLM (iteration 5): fixed precondition and postcondition issues */
    let mut start = 0;
    
    while start < gas.len()
        invariant
            0 <= start <= gas.len(),
            forall|s: int| 0 <= s < start ==> !valid_starting_point(gas, cost, s)
        decreases gas.len() - start
    {
        if check_valid_starting_point(gas, cost, start) {
            proof {
                assert(valid_starting_point(gas, cost, start as int));
                assert(0 <= start < gas.len());
                assert(forall|s: int| 0 <= s < start ==> !valid_starting_point(gas, cost, s));
            }
            return start as i32;
        }
        start = start + 1;
    }
    
    proof {
        assert(forall|s: int| 0 <= s < gas.len() ==> !valid_starting_point(gas, cost, s));
    }
    -1
}
// </vc-code>

}
fn main() {}