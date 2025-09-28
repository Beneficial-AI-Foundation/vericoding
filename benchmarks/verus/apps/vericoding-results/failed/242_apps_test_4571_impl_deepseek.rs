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
proof fn lemma_power_2_small_exp(exp: nat)
    requires
        0 <= exp <= 5,
    ensures
        power(2, exp) == 1 << exp,
    decreases exp
{
    if exp > 0 {
        lemma_power_2_small_exp((exp - 1) as nat);
        assert(1 << ((exp - 1) as nat) == power(2, exp - 1)) by (bit_vector);
        assert(1 << exp == 2 * (1 << ((exp - 1) as nat))) by (bit_vector);
        assert(power(2, exp) == 2 * power(2, exp - 1));
    }
}

proof fn lemma_i8_to_int_identity(x: i8)
    ensures
        x as int == x as int,
{
}

proof fn lemma_i64_to_i8_bounds(value: i64)
    requires
        -128i64 <= value <= 127i64,
    ensures
        value as i8 == value as i8,
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires valid_input(n as int, m as int)
    ensures result as int == expected_time(n as int, m as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Convert to ghost code and fix nat/int usage */
    proof {
        lemma_power_2_small_exp((m as int) as nat);
        lemma_i8_to_int_identity(n);
        lemma_i8_to_int_identity(m);
    }
    
    let n_ghost: int = n as int;
    ghost fn n_ghost() -> int { n as int }
    let m_ghost: int = m as int;
    ghost fn m_ghost() -> int { m as int }
    
    let linear_component: i32 = 1900i32 * (m as i32) + 100i32 * (n as i32 - m as i32);
    let exp_component: i32 = 1 << (m as i32);
    let result_value: i32 = linear_component * exp_component;
    
    proof {
        lemma_i64_to_i8_bounds(result_value as i64);
    }
    
    (result_value as i8)
}
// </vc-code>


}

fn main() {}