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
/* helper modified by LLM (iteration 5): The previous helper section was empty, this one is also empty as no helper functions are needed for this problem. */

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
/* code modified by LLM (iteration 5): Replaced assumption and unreachables with a binary search implementation to find the k-th smallest element. Added proper loop invariants for verification. */
{
    let n_int = n as int;
    let m_int = m as int;
    let k_int = k as int;

    let mut low: int = 1;
    let mut high: int = n_int * m_int;
    let mut ans: int = 0;

    while low <= high
        invariant
            1 <= low,
            low <= n_int * m_int + 1,
            0 <= high,
            high <= n_int * m_int,
            (ans == 0 || (1 <= ans && ans <= n_int * m_int)),
            high < n_int * m_int + 1,
            // For all x in [1, low - 1], count_less_or_equal_value(x) < k.
            forall x: int :: { (1 <= x && x < low) ==> count_less_or_equal_value(n_int, m_int, x) < k_int },
            // If ans is set, then ans is a candidate for the smallest value X such that count_less_or_equal_value(X) >= k. Also, for any value Y > ans, count_less_or_equal_value(Y) >= k.
            // For any value y such that count_less_or_equal_value(y) >= k, then y >= ans (if ans != 0)
            forall y: int :: { (ans != 0 && y >= 1 && y <= n_int * m_int && count_less_or_equal_value(n_int, m_int, y) >= k_int) ==> y >= ans },
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if count_less_or_equal_value(n_int, m_int, mid) >= k_int {
            ans = mid;
            high = mid - 1;
        } else {
            low = mid + 1;
        }
    }
    (ans as i8)
}
// </vc-code>


}

fn main() {}