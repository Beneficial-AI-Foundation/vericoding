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
/* helper modified by LLM (iteration 5): Removed recursive power helper and lemma. Not strictly necessary, as the power spec function can be used directly for verification */

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires valid_input(n as int, m as int)
    ensures result as int == expected_time(n as int, m as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Cast to ghost variables for intermediate calculations, then return as i8. */
{
    let n_ghost: ghost int = n as int;
    let m_ghost: ghost int = m as int;

    let calculated_power_ghost: ghost int = power(2, m_ghost);

    let total_time_ghost: ghost int = (1900 * m_ghost + 100 * (n_ghost - m_ghost)) * calculated_power_ghost;

    (total_time_ghost as i8)
}
// </vc-code>


}

fn main() {}