// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: int, b: int) -> bool {
    n >= 1 && n <= 1000 &&
    m >= 1 && m <= 1000 &&
    a >= 1 && a <= 1000 &&
    b >= 1 && b <= 1000
}

spec fn optimal_cost(n: int, m: int, a: int, b: int) -> int
    recommends valid_input(n, m, a, b)
{
    if n * a <= ((n + m - 1) / m) * b {
        if n * a <= (n / m) * b + (n % m) * a {
            n * a
        } else {
            (n / m) * b + (n % m) * a
        }
    } else {
        if ((n + m - 1) / m) * b <= (n / m) * b + (n % m) * a {
            ((n + m - 1) / m) * b
        } else {
            (n / m) * b + (n % m) * a
        }
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn min3(x: int, y: int, z: int) -> int {
    if x <= y {
        if x <= z { x } else { z }
    } else {
        if y <= z { y } else { z }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int, a as int, b as int),
    ensures 
        result >= 0,
        result as int == optimal_cost(n as int, m as int, a as int, b as int),
// </vc-spec>
// <vc-code>
{
    let ni: int = n as int;
    let mi: int = m as int;
    let ai: int = a as int;
    let bi: int = b as int;

    let cost_all: int = ni * ai;
    let cost_ceil: int = ((ni + mi - 1) / mi) * bi;
    let cost_mix: int = (ni / mi) * bi + (ni % mi) * ai;

    let ans: int = if cost_all <= cost_ceil {
        if cost_all <= cost_mix { cost_all } else { cost_mix }
    } else {
        if cost_ceil <= cost_mix { cost_ceil } else { cost_mix }
    };

    assert(ans == optimal_cost(ni, mi, ai, bi));
    assert(ans >= 0);

    ans as i8
}
// </vc-code>


}

fn main() {}