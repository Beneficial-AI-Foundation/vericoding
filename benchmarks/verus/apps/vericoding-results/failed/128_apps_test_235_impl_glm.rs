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
/* helper modified by LLM (iteration 5): use i16 for intermediate arithmetic to prevent overflow */
fn compute_vasya_eats(n: i8, k: i8) -> (result: i8)
    requires 0 <= n && 1 <= k
    ensures result as int == vasya_eats_with_strategy(n as int, k as int)
    decreases n
{
    if n == 0 {
        0
    } else {
        let cur = if n < k { n } else { k };
        let remaining_after_vasya = (n as i16) - (cur as i16);
        let remaining_after_petya = remaining_after_vasya - remaining_after_vasya / 10;
        let recursive_result = compute_vasya_eats(remaining_after_petya as i8, k);
        (cur as i16 + recursive_result as i16) as i8
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures
        1 <= result as int <= n as int,
        is_minimal_solution(n as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use i8 loop counter and i16 arithmetic for condition check */
{
    let mut k: i8 = 1;
    while k <= n
        invariant
            1 <= k as int <= n as int + 1,
            forall|i: int| 1 <= i < k as int ==> vasya_eats_with_strategy(n as int, i) * 2 < n as int,
        decreases (n as int) - (k as int)
    {
        let eaten = compute_vasya_eats(n, k);
        let total_eaten = eaten as i16;
        let total_n = n as i16;
        if total_eaten * 2 >= total_n {
            return k;
        }
        k += 1;
    }
    n
}
// </vc-code>


}

fn main() {}