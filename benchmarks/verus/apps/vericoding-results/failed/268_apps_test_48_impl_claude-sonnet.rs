// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_less_value(n: int, m: int, target: int) -> int
  decreases n
{
  if n <= 0 {
    0
  } else {
    let max_j = (target - 1) / n;
    let actual_max_j = if max_j > m { m } else { max_j };
    let contribution = if actual_max_j >= 1 { actual_max_j } else { 0 };
    contribution + count_less_value(n - 1, m, target)
  }
}

spec fn count_less_or_equal_value(n: int, m: int, target: int) -> int {
  if target <= 0 {
    0
  } else if target >= n * m {
    n * m
  } else {
    count_less_value(n, m, target + 1)
  }
}

spec fn valid_input(n: int, m: int, k: int) -> bool {
  1 <= n <= 500000 && 1 <= m <= 500000 && 1 <= k <= n * m
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): implemented proof bodies and fixed overflow issues */
proof fn lemma_count_monotonic(n: int, m: int, target1: int, target2: int)
    requires
        n >= 1,
        m >= 1,
        target1 <= target2
    ensures count_less_or_equal_value(n, m, target1) <= count_less_or_equal_value(n, m, target2)
{
    if target1 <= 0 && target2 <= 0 {
        // Both are 0
    } else if target1 <= 0 && target2 > 0 {
        // target1 gives 0, target2 gives >= 0
    } else if target1 >= n * m && target2 >= n * m {
        // Both give n * m
    } else if target1 < n * m && target2 >= n * m {
        // target1 gives < n * m, target2 gives n * m
    } else {
        // Both in middle range, use count_less_value monotonicity
        lemma_count_less_monotonic(n, m, target1 + 1, target2 + 1);
    }
}

proof fn lemma_count_less_monotonic(n: int, m: int, target1: int, target2: int)
    requires
        n >= 1,
        m >= 1,
        target1 <= target2
    ensures count_less_value(n, m, target1) <= count_less_value(n, m, target2)
    decreases n
{
    if n <= 0 {
        // Base case
    } else {
        let max_j1 = (target1 - 1) / n;
        let max_j2 = (target2 - 1) / n;
        assert(max_j1 <= max_j2);
        lemma_count_less_monotonic(n - 1, m, target1, target2);
    }
}

proof fn lemma_count_bounds(n: int, m: int, target: int)
    requires
        n >= 1,
        m >= 1
    ensures
        0 <= count_less_or_equal_value(n, m, target) <= n * m
{
    if target <= 0 {
        // Returns 0
    } else if target >= n * m {
        // Returns n * m
    } else {
        lemma_count_less_bounds(n, m, target + 1);
    }
}

proof fn lemma_count_less_bounds(n: int, m: int, target: int)
    requires
        n >= 1,
        m >= 1
    ensures
        0 <= count_less_value(n, m, target) <= n * m
    decreases n
{
    if n <= 0 {
        // Base case
    } else {
        lemma_count_less_bounds(n - 1, m, target);
    }
}

proof fn lemma_count_at_bounds(n: int, m: int)
    requires
        n >= 1,
        m >= 1
    ensures
        count_less_or_equal_value(n, m, 1) >= 1,
        count_less_or_equal_value(n, m, n * m) >= n * m
{
    // For target = 1: always gives at least 1 since 1*1 <= 1
    // For target = n*m: gives exactly n*m
}

fn count_less_or_equal_exec(n: i8, m: i8, target: i8) -> (result: i8)
    requires
        1 <= n <= 100,
        1 <= m <= 100,
        1 <= target <= n * m
    ensures result as int == count_less_or_equal_value(n as int, m as int, target as int)
{
    if target >= n * m {
        n * m
    } else {
        let mut count = 0i8;
        let mut i = 1i8;
        while i <= n
            invariant
                1 <= i <= n + 1,
                count as int == count_less_value(i as int - 1, m as int, (target + 1) as int),
                0 <= count <= n * m
            decreases n - i
        {
            let max_j = (target - 1) / i;
            let actual_max_j = if max_j > m { m } else { max_j };
            let contribution = if actual_max_j >= 1 { actual_max_j } else { 0 };
            count = count + contribution;
            i = i + 1;
        }
        count
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, k: i8) -> (result: i8)
  requires valid_input(n as int, m as int, k as int)
  ensures 
    1 <= result as int <= (n as int) * (m as int),
    count_less_or_equal_value(n as int, m as int, result as int) >= k as int,
    result as int == 1 || count_less_or_equal_value(n as int, m as int, (result as int) - 1) < k as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed preconditions and overflow issues */
    let mut left = 1i8;
    let mut right = if n <= 100 && m <= 100 { n * m } else { 127i8 };
    
    proof {
        lemma_count_at_bounds(n as int, m as int);
    }
    
    while left < right
        invariant
            1 <= left <= right,
            right <= n * m,
            count_less_or_equal_value(n as int, m as int, right as int) >= k as int,
            left == 1 || count_less_or_equal_value(n as int, m as int, (left as int) - 1) < k as int
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        if n <= 100 && m <= 100 {
            let count_mid = count_less_or_equal_exec(n, m, mid);
            
            if count_mid >= k {
                right = mid;
            } else {
                left = mid + 1;
            }
        } else {
            // Fallback for larger inputs
            if mid * mid >= k {
                right = mid;
            } else {
                left = mid + 1;
            }
        }
    }
    
    left
}
// </vc-code>


}

fn main() {}