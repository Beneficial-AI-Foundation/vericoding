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
/* helper modified by LLM (iteration 5): relate iterative sum with calculate_acc and prove prefixes nonnegative */
proof fn iterative_sum_equals_calc(gas: &Vec<i32>, cost: &Vec<i32>, start: int, steps: int) -> i32
    decreases steps
{
    if steps <= 0 {
        0
    } else {
        let prev = iterative_sum_equals_calc(gas, cost, start, steps - 1);
        let len = gas.len() as int;
        let raw = (start + (steps - 1)) % len;
        let jdx_int = if raw < 0 { raw + len } else { raw };
        let j = jdx_int as usize;
        let res = prev + gas[j] - cost[j];
        assert((res as int) == calculate_acc(gas, cost, start, steps));
        res
    }
}

proof fn prefixes_prove_nonneg(gas: &Vec<i32>, cost: &Vec<i32>, start: int, prefixes: &Vec<i32>, s: nat)
    decreases s
{
    if s == 0 {
    } else {
        prefixes_prove_nonneg(gas, cost, start, prefixes, s - 1);
        let ui: usize = (s - 1) as usize;
        let v = iterative_sum_equals_calc(gas, cost, start, s as int);
        assert(v == prefixes[ui]);
        assert(prefixes[ui] >= 0);
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
    /* code modified by LLM (iteration 5): brute-force search recording prefixes to prove validity */
    let n = gas.len();
    let mut result: i32 = -1;
    if n == 0 {
        return result;
    }
    let mut start_i: usize = 0;
    while start_i < n
        invariant
            start_i <= n,
        decreases n - start_i
    {
        let mut acc: i32 = 0;
        let mut steps: usize = 0;
        let mut failed: bool = false;
        let mut prefixes: Vec<i32> = Vec::new();
        while steps < n
            invariant
                steps <= n,
            decreases n - steps
        {
            let idx = (start_i + steps) % n;
            acc = acc + gas[idx] - cost[idx];
            prefixes.push(acc);
            if acc < 0 {
                failed = true;
                break;
            }
            steps = steps + 1;
        }
        if !failed {
            result = start_i as i32;
            proof {
                prefixes_prove_nonneg(gas, cost, start_i as int, &prefixes, n as nat);
            }
            return result;
        }
        start_i = start_i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}