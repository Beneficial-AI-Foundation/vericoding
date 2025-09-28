// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn power(base: int, exp: int) -> int
  decreases exp when exp >= 0
{
  if exp <= 0 { 1 } else { base * power(base, exp - 1) }
}

spec fn valid_input(n: int, k: int) -> bool
{
  1 <= n <= 1000 && 2 <= k <= 1000
}

spec fn painting_ways(n: int, k: int) -> int
{
  if valid_input(n, k) { k * power(k - 1, n - 1) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
#[verifier::spinoff_prover]
proof fn lemma_power_is_non_negative(base: int, exp: int)
    requires
        base >= 0,
        exp >= 0,
    ensures
        power(base, exp) >= 0,
    decreases exp
{
    if exp > 0 {
        lemma_power_is_non_negative(base, exp - 1);
    }
}

/* helper modified by LLM (iteration 5): fixed path to nonlinear arithmetic lemmas */
#[verifier::spinoff_prover]
proof fn lemma_power_is_positive(base: int, exp: int)
    requires
        base >= 1,
        exp >= 0,
    ensures
        power(base, exp) >= 1,
    decreases exp
{
    if exp == 0 {
        assert(power(base, 0) == 1);
    } else {
        lemma_power_is_positive(base, exp - 1);
        assert(power(base, exp - 1) >= 1);
        assert(base >= 1);
        vstd::arithmetic::nonlinear::mul_le_mono_nonneg(1, base, power(base, exp - 1));
        assert(power(base, exp - 1) <= base * power(base, exp - 1));
        assert(power(base, exp) >= 1);
    }
}

/* helper modified by LLM (iteration 5): fixed path to nonlinear arithmetic lemmas */
#[verifier::spinoff_prover]
proof fn lemma_power_is_monotonic(base: int, exp1: int, exp2: int)
    requires
        base >= 1,
        0 <= exp1 <= exp2,
    ensures
        power(base, exp1) <= power(base, exp2),
    decreases exp2
{
    if exp1 < exp2 {
        lemma_power_is_monotonic(base, exp1, exp2 - 1);
        lemma_power_is_non_negative(base, exp2 - 1);
        assert(power(base, exp2 - 1) >= 0);
        assert(base >= 1);
        vstd::arithmetic::nonlinear::mul_le_mono_nonneg(1, base, power(base, exp2 - 1));
        assert(power(base, exp2 - 1) <= power(base, exp2));
        assert(power(base, exp1) <= power(base, exp2));
    }
}

exec fn exec_power(base: i8, exp: i8) -> (result: i8)
    requires
        exp >= 0,
        base >= 1,
        power(base as int, exp as int) <= 127,
    ensures
        result as int == power(base as int, exp as int),
{
    let mut i: i8 = 0;
    let mut res: i8 = 1;
    while i < exp
        invariant
            0 <= i <= exp,
            base >= 1,
            exp >= 0,
            power(base as int, exp as int) <= 127,
            res as int == power(base as int, i as int),
        decreases exp - i
    {
        proof {
            lemma_power_is_monotonic(base as int, (i + 1) as int, exp as int);
        }
        res = res * base;
        i = i + 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
  requires 
    valid_input(n as int, k as int)
  ensures 
    result as int == painting_ways(n as int, k as int),
    result > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed path to nonlinear arithmetic lemmas */
    let ghost n_int = n as int;
    let ghost k_int = k as int;

    let base = k - 1;
    let exp = n - 1;

    proof {
        let p_val = power(base as int, exp as int);
        assert(k_int >= 2);
        assert(base as int >= 1);
        assert(n_int >= 1);
        assert(exp as int >= 0);
        lemma_power_is_non_negative(base as int, exp as int);

        assert(k_int * p_val == painting_ways(n_int, k_int));
        assert(k_int * p_val <= 127);

        vstd::arithmetic::nonlinear::mul_le_mono_nonneg(2, k_int, p_val);
        assert(2 * p_val <= k_int * p_val);
        assert(2 * p_val <= 127);
        
        assert(p_val <= 63) by {
            if p_val > 63 {
                assert(p_val >= 64);
                vstd::arithmetic::nonlinear::mul_le_mono_nonneg(64, p_val, 2);
                assert(128 <= 2 * p_val);
                assert(false);
            }
        };
        assert(p_val <= 127);
    }
    
    let p = exec_power(base, exp);
    
    proof {
        lemma_power_is_positive(base as int, exp as int);
    }

    let result = k * p;
    result
}
// </vc-code>


}

fn main() {}