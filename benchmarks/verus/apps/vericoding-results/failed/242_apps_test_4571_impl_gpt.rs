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
fn pow2_exec(m: int) -> int
    requires
        0 <= m,
    ensures
        result == power(2, m),
{
    let mut res: int = 1;
    let mut i: int = 0;
    while i < m
        invariant
            0 <= i,
            i <= m,
            res == power(2, i),
        decreases m - i
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
    let n_i: int = n as int;
    let m_i: int = m as int;
    let base: int = 1900 * m_i + 100 * (n_i - m_i);
    let p2: int = pow2_exec(m_i);
    let ans: int = base * p2;
    ans as i8
}
// </vc-code>


}

fn main() {}