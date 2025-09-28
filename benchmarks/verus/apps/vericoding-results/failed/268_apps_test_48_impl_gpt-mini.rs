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
/* helper modified by LLM (iteration 5): compute n*m as spec int */
spec fn nm_i8(n: i8, m: i8) -> int {
    (n as int) * (m as int)
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
/* code modified by LLM (iteration 5): binary search using runtime integers and spec casts in invariants */
{
  let mut l: i64 = 1;
  let mut r: i64 = (n as i64) * (m as i64);

  while l < r
      invariant
          1 <= l as int,
          l as int <= r as int,
          r as int <= nm_i8(n, m),
          count_less_or_equal_value(n as int, m as int, r as int) >= k as int,
          count_less_or_equal_value(n as int, m as int, l as int - 1) < k as int,
      decreases
          (r as int - l as int)
  {
      let mid: i64 = l + (r - l) / 2;

      let mut sum: i64 = 0;
      let mut i2: i64 = 1;

      while i2 <= (n as i64)
          invariant
              0 <= sum as int,
              sum as int <= nm_i8(n, m),
              1 <= i2 as int,
              i2 as int <= (n as int) + 1,
          decreases
              (nm_i8(n, m) - i2 as int + 1)
      {
          let maxj: i64 = mid / i2;
          let mut contrib: i64 = if maxj > (m as i64) { m as i64 } else { maxj };
          if contrib < 0 { contrib = 0; }
          sum = sum + contrib;
          i2 = i2 + 1;
      }

      if sum as int >= k as int {
          r = mid;
      } else {
          l = mid + 1;
      }
  }

  l as i8
}

// </vc-code>


}

fn main() {}