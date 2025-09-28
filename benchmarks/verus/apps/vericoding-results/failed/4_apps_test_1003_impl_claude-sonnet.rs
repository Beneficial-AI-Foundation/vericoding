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
proof fn lemma_socks_decreasing(n: int, m: int, day: int)
    requires
        valid_input(n, m),
        day >= 1,
    ensures
        socks_after_day(n, m, day) == socks_after_day(n, m, day - 1) - 1 + (if day % m == 0 { 1int } else { 0int }),
{
}

proof fn lemma_socks_eventually_zero(n: int, m: int)
    requires
        valid_input(n, m),
    ensures
        exists|d: int| d >= 1 && socks_after_day(n, m, d) <= 0,
{
    let d = n * m + 1;
    assert(socks_after_day(n, m, d) <= 0);
}

proof fn lemma_socks_positive_before(n: int, m: int, day: int)
    requires
        valid_input(n, m),
        day >= 1,
        socks_after_day(n, m, day) <= 0,
    ensures
        forall|k: int| 1 <= k < day ==> socks_after_day(n, m, k) > 0,
{
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
    /* code modified by LLM (iteration 5): separate proof mode computation from exec assignment */
    let mut day: i8 = 1;
    
    while {
        socks_after_day(n as int, m as int, day as int) > 0
    }
        invariant
            day >= 1,
            day <= 127,
            forall|k: int| 1 <= k < day as int ==> socks_after_day(n as int, m as int, k) > 0,
        decreases (n as int * m as int + 1) - day as int
    {
        proof {
            lemma_socks_decreasing(n as int, m as int, day as int + 1);
        }
        day = day + 1;
    }
    
    proof {
        lemma_socks_positive_before(n as int, m as int, day as int);
    }
    
    day
}
// </vc-code>


}

fn main() {}