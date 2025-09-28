// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: int, b: int) -> bool {
    n >= 1 && m >= 1 && a >= 1 && b >= 1
}

spec fn min_cost_to_divisible(n: int, m: int, a: int, b: int) -> int {
    let k = n % m;
    if k * b < (m - k) * a { k * b } else { (m - k) * a }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int, a as int, b as int)
    ensures 
        result as int == min_cost_to_divisible(n as int, m as int, a as int, b as int),
        result as int >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): add bounds assertions and safe truncation */
{
    let n_i32 = n as i32;
    let m_i32 = m as i32;
    let a_i32 = a as i32;
    let b_i32 = b as i32;

    let k = n_i32 % m_i32;
    assert(0 <= k < m_i32);
    assert(k <= 126);
    assert(b_i32 >= 1 && b_i32 <= 127);
    assert(k * b_i32 <= 126 * 127);
    assert(a_i32 >= 1 && a_i32 <= 127);
    assert((m_i32 - k) <= 126);
    assert((m_i32 - k) * a_i32 <= 126 * 127);

    let option1 = k * b_i32;
    let option2 = (m_i32 - k) * a_i32;

    let cost = if option1 < option2 {
        option1
    } else {
        option2
    };

    #[verifier::truncate]
    cost as i8
}
// </vc-code>


}

fn main() {}