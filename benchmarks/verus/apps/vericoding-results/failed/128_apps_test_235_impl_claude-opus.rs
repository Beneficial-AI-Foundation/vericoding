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
proof fn lemma_vasya_eats_monotonic(n: int, k1: int, k2: int)
    requires
        n >= 1,
        1 <= k1 <= k2
    ensures
        vasya_eats_with_strategy(n, k1) <= vasya_eats_with_strategy(n, k2)
    decreases n
{
    if n <= 0 || k1 < 1 {
        return;
    }
    let cur1 = if n < k1 { n } else { k1 };
    let cur2 = if n < k2 { n } else { k2 };
    assert(cur1 <= cur2);
    let remaining_after_vasya1 = n - cur1;
    let remaining_after_vasya2 = n - cur2;
    assert(remaining_after_vasya1 >= remaining_after_vasya2);
    let remaining_after_petya1 = remaining_after_vasya1 - remaining_after_vasya1 / 10;
    let remaining_after_petya2 = remaining_after_vasya2 - remaining_after_vasya2 / 10;
    assert(remaining_after_petya1 >= remaining_after_petya2);
    if remaining_after_petya1 > 0 && remaining_after_petya2 > 0 {
        lemma_vasya_eats_monotonic(remaining_after_petya1, k1, k2);
    }
}

proof fn lemma_vasya_eats_increases(n: int, k: int)
    requires
        n >= 1,
        k >= 1,
        vasya_eats_with_strategy(n, k) * 2 < n
    ensures
        k < n,
        vasya_eats_with_strategy(n, k + 1) * 2 <= n ==> vasya_eats_with_strategy(n, k + 1) > vasya_eats_with_strategy(n, k)
    decreases n
{
    if k >= n {
        assert(vasya_eats_with_strategy(n, k) == n);
        assert(false);
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
{
    /* code modified by LLM (iteration 2): Added decreases clause to inner while loop */
    let mut left: i8 = 1;
    let mut right: i8 = n;
    let mut result: i8 = n;
    
    while left <= right
        invariant
            1 <= left <= n + 1,
            1 <= right <= n,
            1 <= result <= n,
            left <= right + 1,
            vasya_eats_with_strategy(n as int, result as int) * 2 >= n as int,
            forall|k: int| 1 <= k < left ==> vasya_eats_with_strategy(n as int, k) * 2 < n as int,
            forall|k: int| right < k <= n as int ==> vasya_eats_with_strategy(n as int, k) * 2 >= n as int
        decreases right - left + 1
    {
        let mid: i8 = left + (right - left) / 2;
        assert(left <= mid <= right);
        
        let mut total: i8 = 0;
        let mut remaining: i8 = n;
        
        while remaining > 0
            invariant
                0 <= remaining <= n,
                0 <= total <= n,
                total as int + remaining as int <= n as int,
                total as int == vasya_eats_with_strategy(n as int, mid as int) - vasya_eats_with_strategy(remaining as int, mid as int)
            decreases remaining
        {
            let vasya_eats = if remaining < mid { remaining } else { mid };
            total = total + vasya_eats;
            remaining = remaining - vasya_eats;
            let petya_eats = remaining / 10;
            remaining = remaining - petya_eats;
        }
        
        assert(total as int == vasya_eats_with_strategy(n as int, mid as int));
        
        if total * 2 >= n {
            result = mid;
            right = mid - 1;
            proof {
                lemma_vasya_eats_monotonic(n as int, mid as int, n as int);
            }
        } else {
            left = mid + 1;
        }
    }
    
    assert(vasya_eats_with_strategy(n as int, result as int) * 2 >= n as int);
    assert(result as int == 1 || vasya_eats_with_strategy(n as int, result as int - 1) * 2 < n as int);
    result
}
// </vc-code>


}

fn main() {}