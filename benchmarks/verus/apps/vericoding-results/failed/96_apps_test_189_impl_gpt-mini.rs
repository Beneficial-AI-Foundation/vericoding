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
/* helper modified by LLM (iteration 2): compute cost with usize loop and ghost invariant */
fn compute_cost_vec(sticks: &Vec<i8>, t: i8) -> i32
    ensures result as int == cost_for_t(sticks@.map_values(|v: i8| v as int), t as int)
{
    let mut result: i32 = 0;
    let mut idx: usize = 0;
    while idx < sticks.len()
        invariant
            idx <= sticks.len(),
            result as int == cost_for_t(sticks@.map_values(|v: i8| v as int), t as int) - sum_costs(sticks@.map_values(|v: i8| v as int), t as int, idx as int),
        decreases sticks.len() - idx
    {
        let v: i8 = sticks[idx];
        let v_i32: i32 = v as i32;
        let diff_i32: i32 = (t as i32) - v_i32;
        let abs_i32: i32 = if diff_i32 >= 0 { diff_i32 } else { -diff_i32 };
        let term_i32: i32 = if abs_i32 - 1 >= 0 { abs_i32 - 1 } else { 0 };
        result = result + term_i32;
        idx = idx + 1;
    }
    result
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
/* code modified by LLM (iteration 2): iterate t using usize loop and ghost invariants */
{
    // initialize best candidate to t = 1
    let mut best_t: i8 = 1;
    let mut best_cost_i32: i32 = compute_cost_vec(&sticks, best_t);

    let mut t_usize: usize = 2usize;
    while t_usize <= 99usize
        invariant
            1 <= best_t as int <= 99,
            best_cost_i32 as int == cost_for_t(sticks@.map_values(|v: i8| v as int), best_t as int),
            forall|tt: int| 1 <= tt < t_usize as int ==> best_cost_i32 as int <= cost_for_t(sticks@.map_values(|v: i8| v as int), tt as int),
        decreases 100usize - t_usize
    {
        let cand_t: i8 = t_usize as i8;
        let cand_cost: i32 = compute_cost_vec(&sticks, cand_t);
        if cand_cost < best_cost_i32 {
            best_cost_i32 = cand_cost;
            best_t = cand_t;
        }
        t_usize = t_usize + 1;
    }

    (best_t, best_cost_i32 as i8)
}
// </vc-code>


}

fn main() {}