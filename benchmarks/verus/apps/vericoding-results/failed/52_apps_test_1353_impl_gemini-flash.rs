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
/* helper modified by LLM (iteration 5): [Changed return type to i8 and removed `ghost` keyword from parameter type to fix compilation error] */
fn safe_mul(x: i8, y: i8) -> i8
    requires
        x >= 0,
        y >= 0,
        (x as int) * (y as int) <= 2000000000,
    ensures
        safe_mul(x,y) as int == (x as int) * (y as int)
{
    x * y
}
/* helper modified by LLM (iteration 5): [Changed return type to i8 and removed `ghost` keyword from parameter type to fix compilation error] */
fn safe_div(x: i8, y: i8) -> i8
    requires
        x >= 0,
        y >= 1,
    ensures
        safe_div(x,y) as int == (x as int) / (y as int)
{
    x / y
}
/* helper modified by LLM (iteration 5): [Changed return type to i8 and removed `ghost` keyword from parameter type to fix compilation error] */
fn safe_mod(x: i8, y: i8) -> i8
    requires
        x >= 0,
        y >= 1,
    ensures
        safe_mod(x,y) as int == (x as int) % (y as int)
{
    x % y
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
/* code modified by LLM (iteration 5): [Changed type of variables to `ghost int` to fix compilation error] */
{
    let n_int: ghost int = n as int;
    let m_int: ghost int = m as int;
    let a_int: ghost int = a as int;
    let b_int: ghost int = b as int;

    let cost1_ghost = n_int * a_int;

    let num_m_packs_ghost = n_int / m_int;
    let remaining_ghost = n_int % m_int;
    let cost2_ghost = num_m_packs_ghost * b_int + remaining_ghost * a_int;

    let num_m_packs_ceil_ghost = (n_int + m_int - 1) / m_int;
    let cost3_ghost = num_m_packs_ceil_ghost * b_int;

    let res_ghost = if cost1_ghost <= cost2_ghost && cost1_ghost <= cost3_ghost {
        cost1_ghost
    } else if cost2_ghost <= cost1_ghost && cost2_ghost <= cost3_ghost {
        cost2_ghost
    } else {
        cost3_ghost
    };
    
    res_ghost as i8
}
// </vc-code>


}

fn main() {}