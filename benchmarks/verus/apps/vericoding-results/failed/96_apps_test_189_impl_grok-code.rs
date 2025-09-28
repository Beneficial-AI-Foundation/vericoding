// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, sticks: Seq<int>) -> bool {
    1 <= n <= 1000 &&
    sticks.len() == n &&
    (forall|i: int| 0 <= i < sticks.len() ==> #[trigger] sticks[i] >= 1 && #[trigger] sticks[i] <= 100)
}

spec fn cost_for_t(sticks: Seq<int>, t: int) -> int {
    sum_costs(sticks, t, 0)
}

spec fn sum_costs(sticks: Seq<int>, t: int, index: int) -> int
    decreases sticks.len() - index when 0 <= index <= sticks.len()
{
    if index < 0 || index >= sticks.len() {
        0
    } else if index == sticks.len() {
        0
    } else {
        max_int(0, abs_int(t - sticks[index as int]) - 1) + sum_costs(sticks, t, index + 1)
    }
}

spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn max_int(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn is_optimal_t(sticks: Seq<int>, t: int) -> bool {
    forall|other_t: int| 1 <= other_t <= 99 ==> 
        #[trigger] cost_for_t(sticks, t) <= #[trigger] cost_for_t(sticks, other_t)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Introduced exec helper functions for absolute value, maximum, and sum costs computation, using exec types to avoid type errors. */
exec fn abs_i32(x: i32) -> i32
    ensures
        result == abs_int(x as int),
{
    if x >= 0 { x } else { -x }
}

exec fn max_i32(a: i32, b: i32) -> i32
    ensures
        result == max_int(a as int, b as int),
{
    if a >= b { a } else { b }
}

exec fn sum_costs_exec(sticks: &Vec<i8>, t: i8, index: usize) -> i64
    requires
        valid_input(sticks.len() as int, sticks@.map_values(|v: i8| v as int)),
        1 <= t <= 99,
        0 <= index <= sticks.len(),
    ensures
        result as int == sum_costs(sticks@.map_values(|v: i8| v as int), t as int, index as int),
    decreases sticks.len() - index,
{
    if index == sticks.len() {
        0
    } else {
        let diff: i32 = if t >= sticks@[index] {
            (t as i32 - sticks@[index] as i32)
        } else {
            (sticks@[index] as i32 - t as i32)
        };
        let contrib: i64 = if diff - 1 > 0 {
            (diff - 1) as i64
        } else {
            0
        };
        contrib + sum_costs_exec(sticks, t, index + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn find_optimal_t(n: i8, sticks: Vec<i8>) -> (result: (i8, i8))
    requires valid_input(n as int, sticks@.map_values(|v: i8| v as int))
    ensures ({
        let (t, min_cost) = result;
        1 <= t as int <= 99 &&
        min_cost as int >= 0 &&
        min_cost as int == cost_for_t(sticks@.map_values(|v: i8| v as int), t as int) &&
        is_optimal_t(sticks@.map_values(|v: i8| v as int), t as int)
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed syntax error in for loop invariant by replacing chained comparison with && for compatibility with Verus syntax. */
{
    let mut all_costs: Vec<i64> = Vec::with_capacity(99);
    let mut t: i8 = 1;
    while t <= 99
        invariant
            1 <= t <= 100,
            all_costs.len() == (t - 1) as usize,
        decreases (100 - t) as usize,
    {
        let cost = sum_costs_exec(&sticks, t, 0);
        all_costs.push(cost);
        t += 1;
    }
    let mut min_cost: i64 = all_costs[0];
    let mut best_t: i8 = 1;
    for i in 0..all_costs.len()
        invariant
            1 <= best_t <= 99,
            (all_costs.len() == 0 && best_t == 1) || (0 <= (best_t - 1) as usize && (best_t - 1) as usize < all_costs.len()),
            min_cost == all_costs[(best_t - 1) as usize],
            (forall|j: usize| j < i ==> all_costs[j] >= min_cost),
    {
        if all_costs[i] < min_cost {
            min_cost = all_costs[i];
            best_t = (i + 1) as i8;
        }
    }
    (best_t, min_cost as i8)
}
// </vc-code>


}

fn main() {}