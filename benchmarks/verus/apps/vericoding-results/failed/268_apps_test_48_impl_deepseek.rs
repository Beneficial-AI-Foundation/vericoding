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
/* helper modified by LLM (iteration 5): Fixed lemma parameters type issues */
proof fn lemma_count_less_value_monotonic_n(n1: int, n2: int, m: int, target: int)
    requires
        n1 <= n2,
        n1 >= 0,
        m >= 0,
    ensures
        count_less_value(n1, m, target) <= count_less_value(n2, m, target)
{
    if n1 == n2 {
    } else {
        lemma_count_less_value_monotonic_n(n1, n2 - 1, m, target);
    }
}

proof fn lemma_count_less_value_monotonic_m(n: int, m1: int, m2: int, target: int)
    requires
        m1 <= m2,
        n >= 0,
        m1 >= 0,
    ensures
        count_less_value(n, m1, target) <= count_less_value(n, m2, target)
{
    if m1 == m2 {
    } else {
        lemma_count_less_value_monotonic_m(n, m1, m2 - 1, target);
    }
}

proof fn lemma_count_less_value_monotonic_target(n: int, m: int, target1: int, target2: int)
    requires
        target1 <= target2,
        n >= 0,
        m >= 0,
    ensures
        count_less_value(n, m, target1) <= count_less_value(n, m, target2)
{
    if target1 == target2 {
    } else {
        lemma_count_less_value_monotonic_target(n, m, target1, target2 - 1);
    }
}

proof fn lemma_count_less_or_equal_value_monotonic_target(n: int, m: int, k1: int, k2: int)
    requires
        k1 <= k2,
        n >= 1,
        m >= 1,
    ensures
        count_less_or_equal_value(n, m, k1) <= count_less_or_equal_value(n, m, k2)
{
    if k1 == k2 {
    } else {
        lemma_count_less_or_equal_value_monotonic_target(n, m, k1, k2 - 1);
    }
}

proof fn lemma_count_less_value_upper_bound(n: int, m: int, target: int)
    requires
        n >= 0,
        m >= 0,
    ensures
        count_less_value(n, m, target) <= n * m
{
    if n <= 0 {
    } else {
        lemma_count_less_value_upper_bound(n - 1, m, target);
    }
}

proof fn lemma_count_less_value_nonnegative(n: int, m: int, target: int)
    requires
        n >= 0,
        m >= 0,
    ensures
        count_less_value(n, m, target) >= 0
{
    if n <= 0 {
    } else {
        lemma_count_less_value_nonnegative(n - 1, m, target);
    }
}

spec fn in_exec_range(x: int, n: int, m: int) -> bool {
    x >= 1 && x <= n * m
}

proof fn lemma_count_less_exec_compatible(n: int, m: int, target: int)
    requires
        n >= 1,
        m >= 1,
        target >= 0,
    ensures
        count_less_value(n, m, target) >= 0
{
    lemma_count_less_value_nonnegative(n, m, target);
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
    /* code modified by LLM (iteration 5): Fixed lemma call with proper parameter types */
    let mut low: i8 = 1;
    let mut high: i8 = n * m;
    ghost {
        lemma_count_less_or_equal_value_monotonic_target(n as int, m as int, 1, (n * m) as int);
        assert(count_less_or_equal_value(n as int, m as int, high as int) >= k as int);
        assert(count_less_or_equal_value(n as int, m as int, low as int) < k as int);
    }

    while low <= high
        invariant
            low >= 1,
            high <= n * m,
            count_less_or_equal_value(n as int, m as int, low as int) < k as int,
            count_less_or_equal_value(n as int, m as int, high as int) >= k as int
        decreases (high as int) - (low as int)
    {
        let mid: i8 = low + (high - low) / 2;
        ghost {
            lemma_count_less_exec_compatible(n as int, m as int, mid as int);
        }
        let count_mid: int = count_less_or_equal_value(n as int, m as int, mid as int);
        
        if count_mid >= k as int {
            high = mid - 1;
        } else {
            low = mid + 1;
        }
        ghost {
            if count_mid >= k as int {
                assert(count_less_or_equal_value(n as int, m as int, high as int) >= k as int);
            } else {
                assert(count_less_or_equal_value(n as int, m as int, low as int) < k as int);
            }
        }
    }
    
    low
}
// </vc-code>


}

fn main() {}