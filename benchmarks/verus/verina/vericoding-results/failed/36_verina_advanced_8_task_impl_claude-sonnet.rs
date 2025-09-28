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
/* helper modified by LLM (iteration 5): fixed index bounds to match calculate_acc definition */
proof fn lemma_calculate_acc_step(gas: &Vec<i32>, cost: &Vec<i32>, start: int, steps: int)
    requires
        0 <= start < gas.len(),
        steps > 0,
        gas.len() > 0,
        0 <= (start + (steps - 1)) % (gas.len() as int) < gas.len()
    ensures
        calculate_acc(gas, cost, start, steps) == calculate_acc(gas, cost, start, steps - 1) + gas[((start + (steps - 1)) % (gas.len() as int)) as int] - cost[((start + (steps - 1)) % (gas.len() as int)) as int]
{
}

proof fn lemma_acc_monotonic(gas: &Vec<i32>, cost: &Vec<i32>, start: int, step: int)
    requires
        0 <= start < gas.len(),
        0 <= step < gas.len(),
        gas.len() > 0,
        0 <= (start + step) % (gas.len() as int) < gas.len()
    ensures
        calculate_acc(gas, cost, start, step + 1) == calculate_acc(gas, cost, start, step) + gas[((start + step) % (gas.len() as int)) as int] - cost[((start + step) % (gas.len() as int)) as int]
{
}

proof fn lemma_mod_bounds(start: int, step: int, n: int)
    requires
        n > 0,
        0 <= start < n,
        0 <= step < n
    ensures
        0 <= (start + step) % n < n
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
    /* code modified by LLM (iteration 5): fixed bounds checking and overflow issues */
    let n = gas.len();
    let mut start: usize = 0;
    
    while start < n
        invariant
            0 <= start <= n,
            forall|s: int| 0 <= s < start ==> !valid_starting_point(gas, cost, s)
        decreases n - start
    {
        let mut valid = true;
        let mut acc = 0;
        let mut step: usize = 0;
        
        while step < n && valid
            invariant
                0 <= step <= n,
                acc == calculate_acc(gas, cost, start as int, step as int),
                valid ==> (forall|i: int| 0 <= i < step ==> #[trigger] calculate_acc(gas, cost, start as int, i + 1) >= 0)
            decreases n - step
        {
            let idx_calc = (start + step) % n;
            let idx = idx_calc as usize;
            
            proof {
                lemma_mod_bounds(start as int, step as int, n as int);
                assert(0 <= idx_calc < n);
                assert(idx < n);
            }
            
            acc = acc + gas[idx] - cost[idx];
            
            if acc < 0 {
                valid = false;
            }
            step = step + 1;
            
            proof {
                if step > 1 {
                    lemma_acc_monotonic(gas, cost, start as int, (step - 1) as int);
                }
            }
        }
        
        if valid {
            proof {
                assert(step == n);
                assert(forall|i: int| 0 <= i < gas.len() ==> #[trigger] calculate_acc(gas, cost, start as int, i + 1) >= 0);
                assert(valid_starting_point(gas, cost, start as int));
            }
            return start as i32;
        }
        
        start = start + 1;
    }
    
    proof {
        assert(start == n);
        assert(forall|s: int| 0 <= s < gas.len() ==> !valid_starting_point(gas, cost, s));
    }
    
    -1
}
// </vc-code>

}
fn main() {}