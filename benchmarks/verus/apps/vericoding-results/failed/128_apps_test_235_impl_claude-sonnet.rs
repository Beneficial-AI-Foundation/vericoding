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
/* helper modified by LLM (iteration 5): removed return statements from proof blocks */
fn lemma_vasya_monotonic(n: int, k1: int, k2: int)
    requires
        valid_input(n),
        1 <= k1 <= k2
    ensures
        vasya_eats_with_strategy(n, k1) <= vasya_eats_with_strategy(n, k2)
    decreases n
{
    if n <= 0 || k1 < 1 {
        
    } else {
        let cur1 = if n < k1 { n } else { k1 };
        let cur2 = if n < k2 { n } else { k2 };
        let remaining_after_vasya1 = n - cur1;
        let remaining_after_vasya2 = n - cur2;
        let remaining_after_petya1 = remaining_after_vasya1 - remaining_after_vasya1 / 10;
        let remaining_after_petya2 = remaining_after_vasya2 - remaining_after_vasya2 / 10;
        
        if remaining_after_petya1 > 0 && remaining_after_petya2 > 0 {
            lemma_vasya_monotonic(remaining_after_petya1, k1, k2);
        }
    }
}

fn lemma_vasya_upper_bound(n: int, k: int)
    requires
        valid_input(n),
        k >= 1
    ensures
        vasya_eats_with_strategy(n, k) <= n
    decreases n
{
    if n <= 0 || k < 1 {
        
    } else {
        let cur = if n < k { n } else { k };
        let remaining_after_vasya = n - cur;
        let remaining_after_petya = remaining_after_vasya - remaining_after_vasya / 10;
        
        if remaining_after_petya > 0 {
            lemma_vasya_upper_bound(remaining_after_petya, k);
        }
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
    /* code modified by LLM (iteration 5): fixed return statements in proof blocks */
    let mut k = 1i8;
    
    while k <= n
        invariant
            1 <= k <= n + 1,
            valid_input(n as int),
            forall|j: int| 1 <= j < k ==> vasya_eats_with_strategy(n as int, j) * 2 < n as int
    {
        proof {
            lemma_vasya_upper_bound(n as int, k as int);
        }
        
        let vasya_result = {
            let mut total = 0i8;
            let mut remaining = n;
            let mut steps = 0;
            
            while remaining > 0 && steps < 100
                invariant steps >= 0
            {
                let cur = if remaining < k { remaining } else { k };
                total = total + cur;
                remaining = remaining - cur;
                remaining = remaining - remaining / 10;
                steps = steps + 1;
            }
            
            total
        };
        
        if vasya_result * 2 >= n {
            proof {
                lemma_vasya_monotonic(n as int, 1, k as int);
                if k > 1 {
                    assert(vasya_eats_with_strategy(n as int, (k - 1) as int) * 2 < n as int);
                }
            }
            return k;
        }
        k = k + 1;
    }
    
    proof {
        lemma_vasya_upper_bound(n as int, n as int);
        assert(vasya_eats_with_strategy(n as int, n as int) >= n as int);
        assert(false);
    }
    
    n
}
// </vc-code>


}

fn main() {}