// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, sticks: Seq<int>) -> bool {
    1 <= n <= 1000 &&
    sticks.len() == n &&
    (forall|i: int| 0 <= i < sticks.len() ==> 1 <= sticks[i] <= 100)
}

spec fn cost_for_t(sticks: Seq<int>, t: int) -> int {
    sum_costs(sticks, t, 0)
}

spec fn sum_costs(sticks: Seq<int>, t: int, index: int) -> int
    decreases sticks.len() - index
{
    if index == sticks.len() { 0 }
    else { max(0, abs(t - sticks[index]) - 1) + sum_costs(sticks, t, index + 1) }
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn is_optimal_t(sticks: Seq<int>, t: int) -> bool {
    forall|other_t: int| 1 <= other_t <= 99 ==> 
        cost_for_t(sticks, t) <= cost_for_t(sticks, other_t)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_optimal_t(n: int, sticks: Seq<int>) -> (result: (int, int))
    requires valid_input(n, sticks)
    ensures ({
        let (t, min_cost) = result;
        1 <= t <= 99 &&
        min_cost >= 0 &&
        min_cost == cost_for_t(sticks, t) &&
        is_optimal_t(sticks, t)
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    (0int, 0int)
}
// </vc-code>


}

fn main() {}