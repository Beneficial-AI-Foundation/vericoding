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
/* helper modified by LLM (iteration 5): Fixed trigger annotations in compute_cost_for_t requires clause */
fn lemma_cost_for_t_equivalent(sticks: Seq<int>, t: int, n: int)
    requires
        sticks.len() == n,
        n >= 0,
    ensures
        cost_for_t(sticks, t) == sum_costs(sticks, t, 0),
{
}

fn lemma_sum_costs_additive(sticks: Seq<int>, t: int, i: int, j: int)
    requires
        0 <= i <= j <= sticks.len(),
    ensures
        sum_costs(sticks, t, i) == sum_costs(sticks, t, j) + sum_costs(sticks.subrange(i, j), t, 0),
{
}

fn compute_cost_for_t(sticks: &Vec<i8>, t: i8) -> (cost: i8)
    requires
        sticks@.len() >= 0,
        1 <= t <= 99,
        forall|i: int| 0 <= i < sticks@.len() ==> #[trigger] sticks@[i] >= 1 && #[trigger] sticks@[i] <= 100,
    ensures
        cost as int == cost_for_t(sticks@.map_values(|v: i8| v as int), t as int),
{
    let mut total_cost: i8 = 0;
    let mut i = 0;
    
    while i < sticks.len()
        invariant
            0 <= i <= sticks@.len(),
            total_cost as int == sum_costs(sticks@.map_values(|v: i8| v as int), t as int, 0) - sum_costs(sticks@.map_values(|v: i8| v as int), t as int, i as int),
        decreases sticks@.len() - i
    {
        let stick_len = sticks[i];
        let diff = if stick_len >= t { stick_len - t } else { t - stick_len };
        let individual_cost = if diff > 1 { diff - 1 } else { 0 };
        total_cost = total_cost + individual_cost;
        i = i + 1;
    }
    
    total_cost
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
{
    /* code modified by LLM (iteration 5): Fixed trigger annotations in forall quantifier */
    let mut best_t = 1i8;
    let mut min_cost = compute_cost_for_t(&sticks, 1);
    
    let mut t = 2i8;
    while t <= 99
        invariant
            2 <= t <= 100,
            1 <= best_t <= t - 1,
            min_cost as int >= 0,
            min_cost as int == cost_for_t(sticks@.map_values(|v: i8| v as int), best_t as int),
            forall|other_t: int| 1 <= other_t < t ==> #[trigger] cost_for_t(sticks@.map_values(|v: i8| v as int), other_t) >= min_cost as int,
        decreases 100 - t
    {
        let current_cost = compute_cost_for_t(&sticks, t);
        if current_cost < min_cost {
            best_t = t;
            min_cost = current_cost;
        }
        t = t + 1;
    }
    
    proof {
        assert(forall|other_t: int| 1 <= other_t <= 99 ==> #[trigger] cost_for_t(sticks@.map_values(|v: i8| v as int), other_t) >= min_cost as int);
    }
    
    (best_t, min_cost)
}
// </vc-code>


}

fn main() {}