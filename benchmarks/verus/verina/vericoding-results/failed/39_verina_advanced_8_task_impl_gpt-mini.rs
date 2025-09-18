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
/* helper modified by LLM (iteration 5): lemma to unfold calculate_acc by one step */
spec fn calculate_acc_unfold(gas: &Vec<i32>, cost: &Vec<i32>, start: int, steps: int) -> ()
    requires
        0 <= start < gas.len(),
        0 <= steps <= gas.len(),
    ensures
        calculate_acc(gas, cost, start, steps) == if steps <= 0 { 0 } else { calculate_acc(gas, cost, start, steps - 1) + gas[(((start + (steps - 1)) % (gas.len() as int)) as nat % (gas.len() as nat)) as int] - cost[(((start + (steps - 1)) % (gas.len() as int)) as nat % (gas.len() as nat)) as int] },
    decreases steps
{
    proof {
        if steps <= 0 {
            assert(calculate_acc(gas, cost, start, steps) == 0);
        } else {
            calculate_acc_unfold(gas, cost, start, steps - 1);
            let jdx = ((start + (steps - 1)) % (gas.len() as int)) as nat % (gas.len() as nat);
            assert(calculate_acc(gas, cost, start, steps) == calculate_acc(gas, cost, start, steps - 1) + gas[jdx as int] - cost[jdx as int]);
        }
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
/* code modified by LLM (iteration 5): deterministic search using usize runtime counters and ghost ints for specs */
{
    let n_usize: usize = gas.len();
    ghost let n: int = n_usize as int;

    let mut s_usize: usize = 0;
    let mut res: i32 = -1;
    while s_usize < n_usize
        invariant
            0 <= (s_usize as int),
            (s_usize as int) <= n,
            -1 <= (res as int),
            (res as int) < n,
        decreases n - (s_usize as int)
    {
        let mut ok: bool = true;
        let mut step_usize: usize = 1;
        while step_usize <= n_usize
            invariant
                1 <= (step_usize as int),
                (step_usize as int) <= n + 1,
                ok ==> forall|k: int| 1 <= k < (step_usize as int) ==> calculate_acc(gas, cost, (s_usize as int), k) >= 0,
            decreases (n + 1) - (step_usize as int)
        {
            if calculate_acc(gas, cost, (s_usize as int), (step_usize as int)) < 0 {
                ok = false;
                step_usize = n_usize + 1;
            } else {
                step_usize = step_usize + 1;
            }
        }
        if ok {
            res = s_usize as i32;
            s_usize = n_usize;
        } else {
            s_usize = s_usize + 1;
        }
    }

    res
}
// </vc-code>

}
fn main() {}