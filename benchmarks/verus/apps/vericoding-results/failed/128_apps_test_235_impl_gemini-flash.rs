// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn vasya_eats_with_strategy(n: int, k: int) -> int
    decreases n
{
    if n <= 0 || k < 1 { 
        0 
    } else {
        let cur = if n < k { n } else { k };
        let remaining_after_vasya = n - cur;
        let remaining_after_petya = remaining_after_vasya - remaining_after_vasya / 10;
        cur + vasya_eats_with_strategy(remaining_after_petya, k)
    }
}

spec fn is_minimal_solution(n: int, k: int) -> bool {
    valid_input(n) && k >= 1 && 
    vasya_eats_with_strategy(n, k) * 2 >= n &&
    (k == 1 || vasya_eats_with_strategy(n, k - 1) * 2 < n)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures
        1 <= result as int <= n as int,
        is_minimal_solution(n as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch in the `vasya_eats_with_strategy` function call within the loop invariant by explicitly casting mid_ghost to int */
{
    let ghost N_ghost = n as int;
    let mut low: i8 = 1;
    let mut high: i8 = n;
    let mut ans: i8 = n;

    while low <= high
        invariant
            valid_input(N_ghost),
            1 <= low as int,
            high as int <= N_ghost,
            low as int <= high as int + 1,
            ans as int <= N_ghost,
            ans as int >= 1,
            (low == 1 || vasya_eats_with_strategy(N_ghost, (low as int) - 1) * 2 < N_ghost),
            vasya_eats_with_strategy(N_ghost, ans as int) * 2 >= N_ghost
        decreases high - low
    {
        let mid_val = low + (high - low) / 2;
        let ghost mid_ghost = mid_val as int;
        if vasya_eats_with_strategy(N_ghost, mid_ghost) * 2 >= N_ghost {
            ans = mid_val;
            high = mid_val - 1;
        } else {
            low = mid_val + 1;
        }
    }
    ans
}
// </vc-code>


}

fn main() {}