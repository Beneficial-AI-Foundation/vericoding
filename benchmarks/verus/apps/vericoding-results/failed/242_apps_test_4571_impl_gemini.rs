// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int) -> bool {
    1 <= n <= 100 && 1 <= m <= n && m <= 5
}

spec fn power(base: int, exp: int) -> int
    decreases exp when exp >= 0
{
    if exp <= 0 { 1 } else { base * power(base, exp - 1) }
}

spec fn expected_time(n: int, m: int) -> int {
    (1900 * m + 100 * (n - m)) * power(2, m)
}
// </vc-preamble>

// <vc-helpers>
fn power_of_2_exec(exp: i8) -> (result: i32)
    requires
        0 <= exp <= 5,
    ensures
        result as int == power(2, exp as int),
{
    let mut res: i32 = 1;
    let mut i: i8 = 0;
    while i < exp
        invariant
            0 <= exp <= 5,
            0 <= i <= exp,
            res as int == power(2, i as int),
        decreases exp - i
    {
        res = res * 2;
        i = i + 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires valid_input(n as int, m as int)
    ensures result as int == expected_time(n as int, m as int)
// </vc-spec>
// <vc-code>
{
    let p = power_of_2_exec(m);
    let n_i32 = n as i32;
    let m_i32 = m as i32;
    let val = (1800 * m_i32 + 100 * n_i32) * p;
    val as i8
}
// </vc-code>


}

fn main() {}