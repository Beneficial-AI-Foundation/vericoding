// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, t: int) -> bool {
    1 <= n <= 10 && 0 <= t <= 10000
}

spec fn total_glasses(n: int) -> int {
    n * (n + 1) / 2
}

spec fn valid_result(result: int, n: int, t: int) -> bool {
    result >= 0 && result <= total_glasses(n)
}

spec fn correct_for_edge_cases(result: int, n: int, t: int) -> bool {
    (t == 0 ==> result == 0) &&
    (n == 1 && t >= 1 ==> result == 1) &&
    (n == 1 && t == 0 ==> result == 0) &&
    (t >= 1 && n > 1 ==> result >= 1)
}
// </vc-preamble>

// <vc-helpers>
spec fn spec_bin(n: int, k: int) -> int
    requires
        0 <= n (<= 10,
        0 <= k <= n,
    decreases n
{
    if k == 0 {
        1
    } else if k == n {
        1
    } else {
        spec_bin(n-1, k-1) + spec_bin(n-1, k)
    }
}

exec fn calc_bin(n: i64, k: i64) -> i64
    decreases n
    requires
        0 <= n <= 10,
        0 <= k <= n,
    ensures
        calc_bin as int == spec_bin(n as int, k as int),
{
    if k == 0 {
        1
    } else if k == n {
        1
    } else {
        calc_bin(n-1, k-1) + calc_bin(n-1, k)
    }
}

/* helper modified by LLM (iteration 4): kept helpers as is, no modifications needed */

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, t: i8) -> (result: i8)
requires 
    valid_input(n as int, t as int)
ensures 
    valid_result(result as int, n as int, t as int),
    correct_for_edge_cases(result as int, n as int, t as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): removed assumption bypasses, strengthened invariants for verification */
    let mut r: i64 = 1;
    let mut total: i64 = 0;
    let nn = n as i64;
    let tt = t as i64;
    let tg = nn * (nn + 1) / 2;
    while r <= nn
        invariant
            0 <= total <= tg,
            1 <= r <= nn + 1,
            tg == nn * (nn + 1) / 2,
        decreases (nn - r + 1)
    {
        let rr = r - 1;
        let mut kk: i64 = 0;
        let den = if rr == 0 { 1 } else { 1i64 << rr };
        let max_total = kk <= rr;
        while kk <= rr
            invariant
                0 <= kk <= rr + 1,
                max_total == (kk <= rr),
            decreases (rr - kk + 1)
        {
            let b = calc_bin(rr, kk);
            if tt * (b as i64) >= (den as i64) {
                total += 1;
            }
            kk += 1;
        }
        r += 1;
    }
    proof {
        assert(valid_result(total as int, n as int, t as int));
        assert(correct_for_edge_cases(total as int, n as int, t as int));
    }
    (total as i8)
}
// </vc-code>


}

fn main() {}