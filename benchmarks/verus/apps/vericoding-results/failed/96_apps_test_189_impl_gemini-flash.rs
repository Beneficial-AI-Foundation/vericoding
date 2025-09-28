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
/* helper modified by LLM (iteration 5): Fixed type mismatch for `index` parameter */
fn lemma_sum_costs_non_negative(sticks: Seq<int>, t: int, index: int)
    requires
        0 <= index <= sticks.len(),
        (forall|i: int| 0 <= i < sticks.len() ==> #[trigger] sticks[i] >= 1 && #[trigger] sticks[i] <= 100)
    ensures
        sum_costs(sticks, t, index) >= 0
    decreases sticks.len() as int - index
{
    if (index as int) < sticks.len() {
        lemma_sum_costs_non_negative(sticks, t, index + 1);
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
/* code modified by LLM (iteration 5): Fixed type mismatches and casting issues. Changed comparisons from `nat` to `int`. */
{
    let sticks_seq = sticks@.map_values(|v: i8| v as int);

    let mut min_cost: int = 2147483647; 
    let mut optimal_t: int = 1;

    let mut t_candidate: int = 1;
    while t_candidate <= 99
        invariant
            1 <= t_candidate <= 100,
            1 <= optimal_t,
            optimal_t < t_candidate,
            min_cost == cost_for_t(sticks_seq, optimal_t),
            forall|k: int| 1 <= k < t_candidate ==> cost_for_t(sticks_seq, k) >= min_cost,
            min_cost >= 0,
            sticks_seq.len() == n as int,
            (forall|i: int| 0 <= i < sticks_seq.len() ==> sticks_seq[i] >= 1 && sticks_seq[i] <= 100)
        decreases (99 - t_candidate) as int
    {
        let current_cost = cost_for_t(sticks_seq, t_candidate);

        proof {
            lemma_sum_costs_non_negative(sticks_seq, t_candidate, 0);
        }

        if current_cost < min_cost {
            min_cost = current_cost;
            optimal_t = t_candidate;
        }
        t_candidate = t_candidate + 1;
    }

    (optimal_t as i8, min_cost as i8)
}
// </vc-code>


}

fn main() {}