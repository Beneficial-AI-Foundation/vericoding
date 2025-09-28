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
/* helper modified by LLM (iteration 2): added abs_exec function to replace unsupported .abs() method */
fn abs_exec(x: i32) -> i32 {
    if x >= 0 {
        x
    } else {
        -x
    }
}

/* helper modified by LLM (iteration 2): replaced .abs() with abs_exec call */
fn compute_cost(t: i8, sticks: &Vec<i8>) -> i32 {
    let mut total: i32 = 0;
    for i in 0..sticks.len() {
        let diff = abs_exec(t as i32 - sticks[i] as i32);
        let cost = if diff > 1 { diff - 1 } else { 0 };
        total += cost;
    }
    total
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
    /* code modified by LLM (iteration 3): fixed invariant to use spec function instead of exec function */
    let mut best_t: i8 = 1;
    let mut best_cost: i32 = compute_cost(1, &sticks);

    let mut t: i8 = 2;
    while t <= 99
        invariant
            1 <= best_t as int <= 99,
            2 <= t as int <= 100,
            best_cost as int == cost_for_t(sticks@.map_values(|v: i8| v as int), best_t as int),
            forall|k: int| 1 <= k < t as int ==> cost_for_t(sticks@.map_values(|v: i8| v as int), k) >= best_cost as int,
        decreases 100 - t as int
    {
        let cost = compute_cost(t, &sticks);
        if cost < best_cost {
            best_cost = cost;
            best_t = t;
        }
        t += 1;
    }

    (best_t, best_cost as i8)
}
// </vc-code>


}

fn main() {}