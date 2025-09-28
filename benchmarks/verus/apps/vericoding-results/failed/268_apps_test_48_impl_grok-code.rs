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
/* helper modified by LLM (iteration 4): No changes needed, helper function is correct */
fn count_leq(n: i64, m: i64, target: i64) -> (result: i64)
    requires
        1 <= n <= 500000,
        1 <= m <= 500000,
        0 <= target,
    ensures
        result == count_less_or_equal_value(n as int, m as int, target as int),
{
    let mut sum: i64 = 0;
    let mut i: i64 = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            sum == count_less_or_equal_value(i - 1 as int, m as int, target as int),
        decreases (n - i) as nat
    {
        let max_j: i64 = target / i;
        let actual_max_j: i64 = if max_j > m { m } else { max_j };
        let contribution: i64 = if actual_max_j >= 1 { actual_max_j } else { 0 };
        sum = sum + contribution;
        i = i + 1;
    }
    sum
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
    /* code modified by LLM (iteration 4): Fixed type mismatch by casting high to int in invariant */
    let N: i64 = n as i64;
    let M: i64 = m as i64;
    let K: i64 = k as i64;
    let ghost n_int: int = n as int;
    let ghost m_int: int = m as int;
    let ghost k_int: int = k as int;
    let mut low: i64 = 1;
    let mut high: i64 = N * M;
    while low < high
        invariant
            1 <= low <= high + 1,
            high <= N * M,
            forall |x: int| 1 <= x < low ==> count_less_or_equal_value(n_int, m_int, x) < k_int,
            count_less_or_equal_value(n_int, m_int, high as int) >= k_int,
        decreases high - low
    {
        let mid: i64 = (low + high) / 2;
        let cmp: i64 = count_leq(N, M, mid);
        proof {
            assert(cmp == count_less_or_equal_value(n_int, m_int, mid as int));
        }
        if cmp < K {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low as i8
}
// </vc-code>


}

fn main() {}