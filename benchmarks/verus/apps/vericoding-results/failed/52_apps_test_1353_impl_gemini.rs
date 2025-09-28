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
/* helper modified by LLM (iteration 3): This helper is not used but kept for now. */
spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
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
    /* code modified by LLM (iteration 3): use i32 for calculations and add type suffixes */
    let n_i = n as i32;
    let m_i = m as i32;
    let a_i = a as i32;
    let b_i = b as i32;

    let cost1 = n_i * a_i;
    let cost2 = ((n_i + m_i - 1i32) / m_i) * b_i;
    let cost3 = (n_i / m_i) * b_i + (n_i % m_i) * a_i;

    let result_i32 = if cost1 <= cost2 {
        if cost1 <= cost3 {
            cost1
        } else {
            cost3
        }
    } else {
        if cost2 <= cost3 {
            cost2
        } else {
            cost3
        }
    };

    result_i32 as i8
}
// </vc-code>


}

fn main() {}