// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
// Helper lemmas for power of four detection
proof fn lemma_power_of_four_base()
    ensures pow(4, 0) == 1
{
}

proof fn lemma_power_of_four_step(m: nat)
    ensures pow(4, m + 1) == 4 * pow(4, m)
{
}

proof fn lemma_power_of_four_monotonic(m1: nat, m2: nat)
    requires m1 < m2
    ensures pow(4, m1) < pow(4, m2)
{
}

proof fn lemma_power_of_four_min_divisible(n: nat, m: nat)
    requires n == pow(4, m),
        m > 0
    ensures n % 4 == 0
{
}

proof fn lemma_not_power_of_four_if_odd(n: nat)
    requires n % 2 == 1,
        n > 1
    ensures forall|m: nat| n != pow(4, m)
{
}

proof fn lemma_not_power_of_four_if_mod_4_wrong(n: nat)
    requires n % 4 != 0,
        n != 1
    ensures forall|m: nat| n != pow(4, m)
{
}

fn is_power_of_four_recursive(n: nat, current_power: nat, exponent: nat) -> (result: bool)
    requires current_power == pow(4, exponent)
    ensures result <==> (exists|m: nat| m >= exponent && n == pow(4, m))
    decreases (if n >= current_power { n - current_power + 1 } else { 0 })
{
    if current_power == n {
        true
    } else if current_power > n {
        false
    } else {
        is_power_of_four_recursive(n, current_power * 4, exponent + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed nat literal comparisons */
    if n == 1nat {
        proof {
            lemma_power_of_four_base();
            assert(n == pow(4, 0));
        }
        true
    } else if n == 0nat {
        proof {
            lemma_power_of_four_base();
            assert(forall|m: nat| pow(4, m) >= 1);
        }
        false
    } else if n % 4nat != 0nat {
        proof {
            lemma_not_power_of_four_if_mod_4_wrong(n);
        }
        false
    } else {
        is_power_of_four_recursive(n, 1nat, 0nat)
    }
}
// </vc-code>

}
fn main() {}