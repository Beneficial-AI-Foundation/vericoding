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
/* helper modified by LLM (iteration 2): ghost helpers for cumulative differences and overall correctness lemma */
spec fn sum_diff(gas: &Vec<i32>, cost: &Vec<i32>, k: int) -> int
    decreases k
{
    if k <= 0 {
        0
    } else {
        let idx = ((k - 1) % (gas.len() as int)) as nat % (gas.len() as nat);
        sum_diff(gas, cost, k - 1) + gas[idx as int] - cost[idx as int]
    }
}

spec fn total_surplus(gas: &Vec<i32>, cost: &Vec<i32>) -> int {
    sum_diff(gas, cost, gas.len() as int)
}

proof fn algo_correct(gas: &Vec<i32>, cost: &Vec<i32>, res: int)
    requires gas.len() == cost.len() && gas.len() > 0
    ensures
        (res == -1) ==> (forall|start: int| 0 <= start < gas.len() ==> !valid_starting_point(gas, cost, start)),
        (res >= 0) ==> (
            0 <= res < gas.len() &&
            valid_starting_point(gas, cost, res as int) &&
            (forall|start: int| 0 <= start < res ==> !valid_starting_point(gas, cost, start))
        )
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
    /* code modified by LLM (iteration 2): use concrete usize/i64 types to avoid ghost-only 'int'/'nat' in executable code */
    let n = gas.len();
    let mut total: i64 = 0;
    let mut acc: i64 = 0;
    let mut start: usize = 0usize;
    let mut i: usize = 0usize;
    while i < n
        invariant i <= n
        decreases n - i
    {
        let diff_i: i64 = (gas[i] - cost[i]) as i64;
        total += diff_i;
        acc += diff_i;
        if acc < 0 {
            start = i + 1;
            acc = 0;
        }
        i = i + 1;
    }
    if total < 0 {
        -1
    } else {
        start as i32
    }
}

// </vc-code>

}
fn main() {}