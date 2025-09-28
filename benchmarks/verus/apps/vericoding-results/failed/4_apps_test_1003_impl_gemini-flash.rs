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
/* helper modified by LLM (iteration 5): [No helpers available] */

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
/* code modified by LLM (iteration 5): [Changed while loop condition to use ghost variables to resolve type errors for `int` and `nat` outside ghost contexts.] */
{
    let mut days: i8 = 0;
    proof {
        let n_int_ghost = n as int;
        let m_int_ghost = m as int;
        assert(valid_input(n_int_ghost, m_int_ghost));
    }

    while ({ let n_int_ghost = n as int; let m_int_ghost = m as int; socks_after_day(n_int_ghost, m_int_ghost, days as int) > 0 })
        invariant
            days >= 0,
            ({let n_int = n as int; let m_int = m as int; days as int <= n_int + (n_int * m_int)}),
            // The invariant states that the socks can be worn for all days up to the current day.
            forall|k: int| 1 <= k < days as int ==> ({let n_int = n as int; let m_int = m as int; socks_after_day(n_int, m_int, k) > 0}),
            valid_input(n as int, m as int)
        decreases ({let n_int = n as int; let m_int = m as int; (n_int + 1) * m_int - days as int})
    {
        days = days + 1;
    }
    days
}
// </vc-code>


}

fn main() {}