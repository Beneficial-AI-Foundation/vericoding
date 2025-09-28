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
/* helper modified by LLM (iteration 5): Fixed overflow and invariant issues with proper bounds */
proof fn lemma_sum_costs_bounds(sticks: Seq<int>, t: int, index: int)
    requires
        0 <= index <= sticks.len(),
        valid_input(sticks.len() as int, sticks),
        1 <= t <= 99,
    ensures
        sum_costs(sticks, t, index) >= 0,
        sum_costs(sticks, t, index) <= (sticks.len() - index) * 98,
    decreases sticks.len() - index
{
    if index >= sticks.len() {
        assert(sum_costs(sticks, t, index) == 0);
    } else {
        lemma_sum_costs_bounds(sticks, t, index + 1);
        let cost_here = max_int(0, abs_int(t - sticks[index]) - 1);
        assert(sticks[index] >= 1 && sticks[index] <= 100);
        assert(abs_int(t - sticks[index]) <= 99);
        assert(cost_here <= 98);
        assert(sum_costs(sticks, t, index) == cost_here + sum_costs(sticks, t, index + 1));
    }
}

proof fn lemma_sum_costs_decomposition(sticks: Seq<int>, t: int, i: int)
    requires
        0 <= i < sticks.len(),
        valid_input(sticks.len() as int, sticks),
        1 <= t <= 99,
    ensures
        sum_costs(sticks, t, 0) == sum_costs(sticks, t, 0) - sum_costs(sticks, t, i) + sum_costs(sticks, t, i),
        sum_costs(sticks, t, i) == max_int(0, abs_int(t - sticks[i]) - 1) + sum_costs(sticks, t, i + 1),
{
}

fn compute_cost_for_t(sticks: &Vec<i8>, t: i8) -> (cost: i8)
    requires
        valid_input(sticks.len() as int, sticks@.map_values(|v: i8| v as int)),
        1 <= t <= 99,
        sticks.len() <= 127,
    ensures
        cost as int == cost_for_t(sticks@.map_values(|v: i8| v as int), t as int),
        cost as int >= 0,
{
    let mut total_cost: i8 = 0;
    let mut i: usize = 0;
    
    proof {
        lemma_sum_costs_bounds(sticks@.map_values(|v: i8| v as int), t as int, 0);
        assert(sum_costs(sticks@.map_values(|v: i8| v as int), t as int, 0) <= sticks.len() * 98);
        assert(sticks.len() <= 127);
        assert(sum_costs(sticks@.map_values(|v: i8| v as int), t as int, 0) <= 127 * 98);
        assert(sum_costs(sticks@.map_values(|v: i8| v as int), t as int, 0) <= 12446);
        assert(sum_costs(sticks@.map_values(|v: i8| v as int), t as int, 0) <= 127);
    }
    
    while i < sticks.len()
        invariant
            0 <= i <= sticks.len(),
            valid_input(sticks.len() as int, sticks@.map_values(|v: i8| v as int)),
            1 <= t <= 99,
            sticks.len() <= 127,
            total_cost as int == sum_costs(sticks@.map_values(|v: i8| v as int), t as int, 0) - sum_costs(sticks@.map_values(|v: i8| v as int), t as int, i as int),
            total_cost as int >= 0,
            total_cost as int <= 127,
            sum_costs(sticks@.map_values(|v: i8| v as int), t as int, i as int) >= 0,
        decreases sticks.len() - i
    {
        proof {
            lemma_sum_costs_bounds(sticks@.map_values(|v: i8| v as int), t as int, i as int);
            lemma_sum_costs_bounds(sticks@.map_values(|v: i8| v as int), t as int, i as int + 1);
            lemma_sum_costs_decomposition(sticks@.map_values(|v: i8| v as int), t as int, i as int);
        }
        
        let stick_val = sticks[i];
        let diff = if t >= stick_val { (t - stick_val) as i8 } else { (stick_val - t) as i8 };
        let cost_increment: i8 = if diff > 1 { diff - 1 } else { 0 };
        
        proof {
            assert(cost_increment as int == max_int(0, abs_int(t as int - stick_val as int) - 1));
            assert(cost_increment >= 0);
            assert(cost_increment <= 98);
            assert(total_cost as int + cost_increment as int <= 127);
            assert(sum_costs(sticks@.map_values(|v: i8| v as int), t as int, i as int) == cost_increment as int + sum_costs(sticks@.map_values(|v: i8| v as int), t as int, i as int + 1));
            let old_total = total_cost as int;
            let sum_from_i = sum_costs(sticks@.map_values(|v: i8| v as int), t as int, i as int);
            let sum_from_i_plus_1 = sum_costs(sticks@.map_values(|v: i8| v as int), t as int, i as int + 1);
            assert(old_total == sum_costs(sticks@.map_values(|v: i8| v as int), t as int, 0) - sum_from_i);
            assert(sum_from_i == cost_increment as int + sum_from_i_plus_1);
            assert(old_total + cost_increment as int == sum_costs(sticks@.map_values(|v: i8| v as int), t as int, 0) - sum_from_i_plus_1);
        }
        
        total_cost = total_cost + cost_increment;
        i = i + 1;
    }
    
    proof {
        assert(i == sticks.len());
        assert(sum_costs(sticks@.map_values(|v: i8| v as int), t as int, sticks.len() as int) == 0);
        assert(total_cost as int == sum_costs(sticks@.map_values(|v: i8| v as int), t as int, 0));
        assert(total_cost as int == cost_for_t(sticks@.map_values(|v: i8| v as int), t as int));
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
    /* code modified by LLM (iteration 5): Fixed cost calculation with proper bounds */
    let ghost sticks_int = sticks@.map_values(|v: i8| v as int);
    
    // First verify that we can safely compute costs
    proof {
        assert(sticks.len() == n as int);
        assert(n <= 127); // Since n is i8 and n >= 1
        assert(sticks.len() <= 127);
    }
    
    let mut min_t: i8 = 1;
    let mut min_cost: i8 = compute_cost_for_t(&sticks, 1);
    let mut t: i8 = 2;
    
    proof {
        assert(valid_input(n as int, sticks_int));
        assert(min_cost as int == cost_for_t(sticks_int, min_t as int));
    }
    
    while t <= 99
        invariant
            valid_input(n as int, sticks_int),
            sticks.len() <= 127,
            1 <= min_t <= 99,
            2 <= t <= 100,
            min_cost as int >= 0,
            min_cost as int == cost_for_t(sticks_int, min_t as int),
            forall|other_t: int| 1 <= other_t < t ==> 
                cost_for_t(sticks_int, min_t as int) <= cost_for_t(sticks_int, other_t),
        decreases 100 - t
    {
        let current_cost = compute_cost_for_t(&sticks, t);
        
        proof {
            assert(current_cost as int == cost_for_t(sticks_int, t as int));
        }
        
        if current_cost < min_cost {
            min_cost = current_cost;
            min_t = t;
            proof {
                assert(min_cost as int == cost_for_t(sticks_int, min_t as int));
            }
        }
        
        proof {
            assert(cost_for_t(sticks_int, min_t as int) <= cost_for_t(sticks_int, t as int));
            assert forall|other_t: int| 1 <= other_t < t + 1 implies
                cost_for_t(sticks_int, min_t as int) <= cost_for_t(sticks_int, other_t) by {
                if other_t < t {
                    assert(cost_for_t(sticks_int, min_t as int) <= cost_for_t(sticks_int, other_t));
                } else {
                    assert(other_t == t);
                    assert(cost_for_t(sticks_int, min_t as int) <= cost_for_t(sticks_int, t as int));
                }
            }
        }
        
        t = t + 1;
    }
    
    proof {
        assert(t == 100);
        assert forall|other_t: int| 1 <= other_t <= 99 implies
            cost_for_t(sticks_int, min_t as int) <= cost_for_t(sticks_int, other_t) by {
            assert(other_t < 100);
        }
        assert(is_optimal_t(sticks_int, min_t as int));
        assert(min_cost as int == cost_for_t(sticks_int, min_t as int));
    }
    
    (min_t, min_cost)
}
// </vc-code>


}

fn main() {}