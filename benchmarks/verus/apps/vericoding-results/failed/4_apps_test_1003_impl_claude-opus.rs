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
    /* code modified by LLM (iteration 5): fixed quantifier trigger annotation */
    let mut day: i8 = 0;
    let mut socks: i8 = n;
    
    while socks > 0
        invariant
            0 <= day <= 127,
            valid_input(n as int, m as int),
            socks >= 0,
            socks as int == socks_after_day(n as int, m as int, day as int),
            forall|k: int| #[trigger] (1 <= k <= day as int) ==> socks_after_day(n as int, m as int, k - 1) > 0 || k == 1,
        decreases 127 - day
    {
        if day == 127 {
            // Prevent overflow
            break;
        }
        
        // Calculate next day's socks
        let old_socks = socks;
        day = day + 1;
        
        // We wear one sock
        socks = socks - 1;
        
        // If it's an m-th day, we buy a new sock
        if day % m == 0 {
            socks = socks + 1;
        }
        
        proof {
            // Verify the invariant is maintained
            assert(socks as int == old_socks as int - 1 + if day as int % m as int == 0 { 1int } else { 0int });
            assert(socks as int == n as int + (day as int) / (m as int) - day as int);
            assert(socks as int == socks_after_day(n as int, m as int, day as int));
        }
    }
    
    proof {
        assert(socks as int == socks_after_day(n as int, m as int, day as int));
        assert(socks as int <= 0);
        assert(day as int >= n as int);
        if day as int > 0 {
            assert(socks_after_day(n as int, m as int, day as int - 1) >= socks_after_day(n as int, m as int, day as int) + 1);
            assert(socks_after_day(n as int, m as int, day as int - 1) > 0);
        }
    }
    
    day
}
// </vc-code>


}

fn main() {}