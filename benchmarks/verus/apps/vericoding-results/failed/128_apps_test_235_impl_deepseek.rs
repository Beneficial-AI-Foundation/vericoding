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
proof fn lemma_minimal_solution_exists(n: int)
    requires n >= 1
    ensures exists|k: int| 1 <= k <= n && is_minimal_solution(n, k)
{
    // Proof that a minimal solution exists
    assert(vasya_eats_with_strategy(n, n) * 2 >= n);
    if n == 1 {
        assert(is_minimal_solution(n, 1));
    } else {
        assert(vasya_eats_with_strategy(n, 1) * 2 >= 1);
    }
}

proof fn lemma_binary_search_works(n: int, low: int, high: int)
    requires
        n >= 1,
        1 <= low <= high <= n,
        vasya_eats_with_strategy(n, low) * 2 >= n,
        vasya_eats_with_strategy(n, high) * 2 < n,
    ensures
        low < high
{
    if low >= high {
        assert(low == high);
        assert(vasya_eats_with_strategy(n, low) * 2 >= n);
        assert(vasya_eats_with_strategy(n, high) * 2 < n);
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
    /* code modified by LLM (iteration 5): Fix compilation errors and implement binary search */
    proof {
        lemma_minimal_solution_exists(n as int);
    }
    
    let mut low: i8 = 1;
    let mut high: i8 = n;
    
    while low < high
        invariant
            1 <= low <= high <= n,
            vasya_eats_with_strategy(n as int, low as int) * 2 >= n as int,
            vasya_eats_with_strategy(n as int, high as int) * 2 < n as int,
        decreases (high - low) as int
    {
        let mid: i8 = low + (high - low) / 2;
        let ghost eaten = vasya_eats_with_strategy(n as int, mid as int);
        
        if eaten * 2 >= n as int {
            high = mid;
        } else {
            low = mid + 1;
            proof {
                lemma_binary_search_works(n as int, low as int, high as int);
            }
        }
    }
    
    assert(low == high);
    assert(vasya_eats_with_strategy(n as int, low as int) * 2 >= n as int);
    low
}
// </vc-code>


}

fn main() {}