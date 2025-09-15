// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type mismatches by using proper nat operations and remove invalid functions */
proof fn lemma_pow4_greater_than_zero(m: nat) 
    ensures pow(4, m) > 0
{
    if m > 0 {
        lemma_pow4_greater_than_zero((m as int - 1) as nat);
    }
}

proof fn lemma_pow4_injective(m1: nat, m2: nat)
    requires pow(4, m1) == pow(4, m2)
    ensures m1 == m2
{
    if m1 != m2 {
        if m1 > m2 {
            lemma_pow4_injective((m1 as int - 1) as nat, m2);
        } else {
            lemma_pow4_injective(m1, (m2 as int - 1) as nat);
        }
    }
}

spec fn is_nat_zero(n: nat) -> bool { n == 0 }
spec fn is_nat_one(n: nat) -> bool { n == 1 }
spec fn nat_mod_four(n: nat) -> nat { n % 4 }
spec fn nat_div_four(n: nat) -> nat { n / 4 }
// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use proper nat operations and add verification conditions */
{
    if n == 0 {
        false
    } else if n == 1 {
        true
    } else {
        let mod_result = n % 4;
        if mod_result != 0 {
            false
        } else {
            let next_n = n / 4;
            if_power_of_four(next_n)
        }
    }
}
// </vc-code>

}
fn main() {}