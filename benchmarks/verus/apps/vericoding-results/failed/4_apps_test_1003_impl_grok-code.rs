// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
    n >= 1 && m >= 2
}

spec fn socks_after_day(n: int, m: int, day: int) -> int {
    if m > 0 {
        n + day / m - day
    } else {
        0
    }
}

spec fn can_wear_socks_on_day(n: int, m: int, day: int) -> bool {
    if m > 0 {
        day >= 1 ==> socks_after_day(n, m, day - 1) > 0
    } else {
        false
    }
}
// </vc-preamble>

// <vc-helpers>
fn socks_after_day_exe(n: i8, m: i8, day: i32) -> i64 {
    if m > 0 {
        (n as i64 + (day as i64) / (m as i64) - (day as i64))
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
  requires 
      valid_input(n as int, m as int)
  ensures 
      result as int >= n as int,
      result as int > 0,
      socks_after_day(n as int, m as int, result as int) <= 0,
      forall|k: int| 1 <= k < result as int ==> socks_after_day(n as int, m as int, k) > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Changed d to i32 and used exec helper for socks_after_day calculation */
    let mut d: i32 = 0;
    while socks_after_day_exe(n, m, d + 1) > 0
        invariant
            0 <= d,
            forall|k: int| 1 <= k <= d as int ==> socks_after_day(n as int, m as int, k) > 0,
            d as int <= n as int,
        decreases n as int - d as int
    {
        d = d + 1;
    }
    (d as i8)
}
// </vc-code>


}

fn main() {}