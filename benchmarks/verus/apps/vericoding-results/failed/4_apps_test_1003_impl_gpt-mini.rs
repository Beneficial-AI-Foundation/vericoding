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
/* helper modified by LLM (iteration 3): prove socks eventually zero at day n*m */
proof fn socks_eventually_zero(n: int, m: int)
    requires
        n >= 1,
        m >= 2,
    ensures
        socks_after_day(n, m, n * m) <= 0,
{
    let q: int = (n * m) / m;
    // division quotient bounds: q * m <= n * m < (q + 1) * m
    assert(q * m <= n * m);
    assert(n * m < (q + 1) * m);

    // from q * m <= n * m deduce q <= n
    assert((q - n) * m <= 0);
    assert(m > 0);
    // since m > 0 and (q - n) * m <= 0, we get q - n <= 0
    assert(q <= n);

    // from n * m < (q + 1) * m deduce n <= q
    assert(n * m - (q + 1) * m < 0);
    assert((n - q - 1) * m < 0);
    // since m > 0, (n - q - 1) < 0 implies n - q <= 0, i.e., n <= q
    assert(n <= q);

    // combine to equality
    assert(q == n);

    // compute socks_after_day and conclude non-positivity
    assert(socks_after_day(n, m, n * m) == n + q - n * m);
    assert(socks_after_day(n, m, n * m) == 2 * n - n * m);
    assert(2 * n - n * m <= 0);
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
    /* code modified by LLM (iteration 3): runtime search with ghost invariants and proof of minimality */

    let ghost n_i: int = n as int;
    let ghost m_i: int = m as int;

    let n_i32: i32 = n as i32;
    let m_i32: i32 = m as i32;
    let mut day_r: i32 = 0;

    // m >= 2 from the precondition, so casted runtime value is positive
    assert(m_i32 > 0);

    while n_i32 + day_r / m_i32 - day_r > 0
        invariant
            0 <= day_r as int && day_r as int <= n_i * m_i,
            forall|k: int| 1 <= k < day_r as int ==> socks_after_day(n_i, m_i, k) > 0,
        decreases
            n_i * m_i - day_r as int
    {
        day_r = day_r + 1;
    }

    let result: i8 = day_r as i8;

    proof {
        let day: int = day_r as int;
        // exit condition yields non-positivity of socks at 'day'
        assert((n_i32 + day_r / m_i32 - day_r) as int <= 0);
        assert(socks_after_day(n_i, m_i, day) <= 0);
        // invariant gives positivity for all earlier days (k in [1, day))
        assert(forall|k: int| 1 <= k < day ==> socks_after_day(n_i, m_i, k) > 0);
        // result bounds
        assert(result as int >= n as int);
        assert(result as int > 0);
    }

    result
}
// </vc-code>


}

fn main() {}