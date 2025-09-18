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
/* helper modified by LLM (iteration 5): fixed type mismatches in index calculations */
fn lemma_calculate_acc_monotonic(gas: &Vec<i32>, cost: &Vec<i32>, start: int, steps: int)
    requires
        0 <= start < gas.len(),
        0 <= steps < gas.len(),
    ensures
        calculate_acc(gas, cost, start, steps + 1) == calculate_acc(gas, cost, start, steps) + gas[((start + steps) % (gas.len() as int)) as int] - cost[((start + steps) % (gas.len() as int)) as int],
{
}

fn lemma_valid_starting_point_acc(gas: &Vec<i32>, cost: &Vec<i32>, start: int)
    requires
        0 <= start < gas.len(),
    ensures
        valid_starting_point(gas, cost, start) <==> (forall|i: int| 0 <= i < gas.len() ==> calculate_acc(gas, cost, start, i + 1) >= 0),
{
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
    /* code modified by LLM (iteration 5): fixed type mismatches for function arguments */
    let mut start = 0;
    while start < gas.len()
        invariant
            0 <= start <= gas.len(),
            forall|i: int| 0 <= i < start ==> !valid_starting_point(gas, cost, i),
        decreases gas.len() - start
    {
        let mut acc = 0;
        let mut steps = 0;
        let mut valid = true;
        
        while steps < gas.len() && valid
            invariant
                0 <= start < gas.len(),
                0 <= steps <= gas.len(),
                valid ==> (forall|i: int| 0 <= i < steps ==> calculate_acc(gas, cost, start as int, i + 1) >= 0),
                !valid ==> exists|i: int| 0 <= i < steps && calculate_acc(gas, cost, start as int, i + 1) < 0,
                acc == calculate_acc(gas, cost, start as int, steps as int),
            decreases gas.len() - steps
        {
            let jdx = (start + steps) % gas.len();
            acc = acc + gas[jdx] - cost[jdx];
            steps = steps + 1;
            
            if acc < 0 {
                valid = false;
            }
            
            proof {
                lemma_calculate_acc_monotonic(gas, cost, start as int, (steps - 1) as int);
            }
        }
        
        if valid && steps == gas.len() {
            proof {
                lemma_valid_starting_point_acc(gas, cost, start as int);
                assert(valid_starting_point(gas, cost, start as int));
            }
            return start as i32;
        }
        
        start = start + 1;
    }
    
    -1
}
// </vc-code>

}
fn main() {}