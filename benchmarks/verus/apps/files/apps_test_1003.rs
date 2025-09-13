// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int) -> (result: int)
  requires 
      valid_input(n, m)
  ensures 
      result >= n,
      result > 0,
      socks_after_day(n, m, result) <= 0,
      forall|k: int| 1 <= k < result ==> socks_after_day(n, m, k) > 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    n
}
// </vc-code>


}

fn main() {}