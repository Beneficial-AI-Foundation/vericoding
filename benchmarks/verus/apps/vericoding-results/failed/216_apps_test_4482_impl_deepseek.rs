// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_squares(p: int, a: Seq<int>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        (p - a[0]) * (p - a[0]) + sum_squares(p, a.subrange(1, a.len() as int))
    }
}

spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && n <= 100 && a.len() == n && 
    forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= -100 && #[trigger] a[i] <= 100
}

spec fn is_optimal_cost(result: int, a: Seq<int>) -> bool {
    result >= 0 &&
    exists|p: int| -100 <= p <= 100 && result == sum_squares(p, a) &&
    forall|p: int| -100 <= p <= 100 ==> result <= sum_squares(p, a)
}
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Fixed type conversion issues and removed nat/int ghost code */
use vstd::calc_macro::calc;

spec fn sum_squares_range(p: int, a: Seq<int>, low: int, high: int) -> int
    decreases high - low
{
    if low >= high {
        0
    } else {
        (p - a[low]) * (p - a[low]) + sum_squares_range(p, a, low + 1, high)
    }
}

proof fn sum_squares_matches_range(p: int, a: Seq<int>)
    ensures
        sum_squares(p, a) == sum_squares_range(p, a, 0, a.len()),
{
    let n = a.len();
    
    assert forall|k: int| 0 <= k <= n implies sum_squares(p, a.subrange(k, n)) == sum_squares_range(p, a, k, n) by {
        if k < n {
            calc! {
                sum_squares(p, a.subrange(k, n));
                    == (p - a[k]) * (p - a[k]) + sum_squares(p, a.subrange(k + 1, n));
                    == (p - a[k]) * (p - a[k]) + sum_squares_range(p, a, k + 1, n);
                    == sum_squares_range(p, a, k, n);
            }
        } else {
            assert(a.subrange(k, n).len() == 0);
            assert(sum_squares_range(p, a, k, n) == 0);
        }
    };
    
    assert(sum_squares(p, a) == sum_squares_range(p, a, 0, n));
}

proof fn sum_squares_range_additive(p: int, a: Seq<int>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= a.len(),
    ensures
        sum_squares_range(p, a, i, k) == sum_squares_range(p, a, i, j) + sum_squares_range(p, a, j, k),
{
    if i == j {
        assert(sum_squares_range(p, a, i, j) == 0);
    } else {
        calc! {
            sum_squares_range(p, a, i, k);
                == (p - a[i]) * (p - a[i]) + sum_squares_range(p, a, i + 1, k);
                == (p - a[i]) * (p - a[i]) + sum_squares_range(p, a, i + 1, j) + sum_squares_range(p, a, j, k);
                == sum_squares_range(p, a, i, j) + sum_squares_range(p, a, j, k);
        }
    }
}

fn compute_sum_squares(p: i8, a: &Vec<i8>, low: usize, high: usize) -> (result: i32)
    requires
        a@.len() >= high >= low >= 0,
        p as int >= -100,
        p as int <= 100,
        forall|i: int| 0 <= i < a@.len() ==> #[trigger] a@[i] >= -100 && #[trigger] a@[i] <= 100,
    ensures
        result as int == sum_squares_range(p as int, a@.map(|_i: int, x: i8| x as int), low as int, high as int),
        result >= 0,
{
    let mut sum: i32 = 0;
    let mut idx: usize = low;
    
    while idx < high
        invariant
            low <= idx <= high,
            sum_squares_range(p as int, a@.map(|_i: int, x: i8| x as int), low as int, idx as int) == sum as int,
            sum >= 0,
    {
        let x = a[idx] as i32;
        let p_i32 = p as i32;
        let diff = p_i32 - x;
        let term = diff * diff;
        
        let next_sum = sum + term;
        sum = next_sum;
        idx = idx + 1;
        
        let prev_idx = idx - 1;
        
        proof {
            let ghost_seq = a@.map(|_i: int, x: i8| x as int);
            sum_squares_range_additive(
                p as int, 
                ghost_seq, 
                low as int, 
                prev_idx as int, 
                idx as int
            );
            
            let single_term = (p as i32 - a[prev_idx] as i32) * (p as i32 - a[prev_idx] as i32);
            assert(sum_squares_range(p as int, ghost_seq, prev_idx as int, idx as int) == single_term as int);
            assert(single_term == term);
            
            assert(sum as int == sum_squares_range(p as int, ghost_seq, low as int, idx as int));
        }
    }
    
    sum
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|_i: int, x: i8| x as int))
    ensures is_optimal_cost(result as int, a@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax errors and proper function calls */
    let mut best_cost: i32 = 1000000000;
    let mut best_p: i8 = -100;
    
    let mut current_p: i8 = -100;
    
    while current_p <= 100
        invariant
            -100 <= current_p <= 101,
            best_cost >= 0,
            exists|p: int| -100 <= p <= current_p - 1 && best_cost as int == sum_squares(p, a@.map(|_i: int, x: i8| x as int)),
            forall|p: int| -100 <= p <= current_p - 1 ==> best_cost as int <= sum_squares(p, a@.map(|_i: int, x: i8| x as int)),
    {
        let cost = compute_sum_squares(current_p, &a, 0, a.len());
        
        if cost < best_cost {
            best_cost = cost;
            best_p = current_p;
        }
        
        assert(best_cost as int <= sum_squares(current_p as int, a@.map(|_i: int, x: i8| x as int)));
        
        current_p = current_p + 1;
    }
    
    assert(current_p == 101);
    assert(-100 <= best_p <= 100);
    assert(best_cost as int == sum_squares(best_p as int, a@.map(|_i: int, x: i8| x as int)));
    assert(forall|p: int| -100 <= p <= 100 ==> best_cost as int <= sum_squares(p, a@.map(|_i: int, x: i8| x as int)));
    
    let result = best_cost as i8;
    result
}
// </vc-code>


}

fn main() {}